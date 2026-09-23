"""Independent algorithm/bytecode comparison. SHA-256 is a test oracle, not a ROM proof."""
import hashlib
import json
from pathlib import Path
from build import build, HEIGHT, CHAINS, SIGNATURE_BYTES, WITNESS_BASE, RANDOMIZER_BYTES

MASK = (1 << 64) - 1

class Oracle:
    def __init__(self, zero=False):
        self.calls = self.compressions = 0
        self.zero = zero
    def __call__(self, data):
        self.calls += 1
        self.compressions += max(1, (len(data) + 63) // 64)
        return bytes(32) if self.zero else hashlib.sha256(data).digest()

def query(h, tag, level, tree, payload, leaf=0, chain=0, step=0):
    word = tag | (level << 8) | (leaf << 16) | (chain << 24) | (step << 32)
    return h(word.to_bytes(8, 'little') + tree.to_bytes(24, 'little') + payload)

def digits(digest):
    x = int.from_bytes(digest, 'little')
    result = [(x >> (3 * j)) & 7 for j in range(43)]
    checksum = 301 - sum(result)
    return result + [(checksum >> (3 * j)) & 7 for j in range(3)]

def leaf(h, secret_key, level, tree, side, message):
    if level == 0:
        secret = query(h, 1, level, tree, secret_key, side)[:16]
        return query(h, 2, level, tree, secret, side)[:16], secret
    encoded = digits(message)
    endpoints, signature = [], []
    for chain in range(CHAINS):
        value = query(h, 1, level, tree, secret_key, side, chain)[:16]
        values = [value]
        for step in range(7):
            value = query(h, 2, level, tree, value, side, chain, step)[:16]
            values.append(value)
        endpoints.append(value)
        signature.append(values[encoded[chain]])
    root = query(h, 3, level, tree, b''.join(endpoints), side)[:16]
    return root, b''.join(signature)

def tree(h, secret_key, level, address, selected, message):
    pair = [leaf(h, secret_key, level, address, side, message) for side in range(2)]
    root = query(h, 4, level, address, pair[0][0] + pair[1][0])[:16]
    return root, pair[selected][1] + pair[1 - selected][0]

def keygen(h, secret_key):
    return tree(h, secret_key, HEIGHT - 1, 0, 0, bytes(16))[0]

def sign(h, secret_key, public_key, message):
    randomizer = query(h, 6, 0, 0, secret_key + message)
    index = int.from_bytes(query(h, 5, 0, 0, public_key + message + randomizer)[:20], 'little')
    current, layers = bytes(16), []
    for level in range(HEIGHT):
        selected = index & 1
        index >>= 1
        current, signature = tree(h, secret_key, level, index, selected, current)
        layers.append(signature)
    return randomizer + b''.join(layers) if current == public_key else None

def verify(h, public_key, message, signature):
    if len(signature) != SIGNATURE_BYTES: return False
    randomizer = signature[:RANDOMIZER_BYTES]
    index = int.from_bytes(query(h, 5, 0, 0, public_key + message + randomizer)[:20], 'little')
    current, offset = bytes(16), RANDOMIZER_BYTES
    for level in range(HEIGHT):
        selected = index & 1
        index >>= 1
        if level == 0:
            value = signature[offset:offset+16]
            offset += 16
            current = query(h, 2, level, index, value, selected)[:16]
        else:
            endpoints = []
            for chain, start in enumerate(digits(current)):
                value = signature[offset:offset+16]
                offset += 16
                for step in range(start, 7):
                    value = query(h, 2, level, index, value, selected, chain, step)[:16]
                endpoints.append(value)
            current = query(h, 3, level, index, b''.join(endpoints), selected)[:16]
        sibling = signature[offset:offset+16]
        offset += 16
        pair = current + sibling if selected == 0 else sibling + current
        current = query(h, 4, level, index, pair)[:16]
    return offset == len(signature) and current == public_key

def signed(x, bits):
    return x - (1 << bits) if x & (1 << (bits - 1)) else x

class Machine:
    def __init__(self, phase, inputs, zero=False):
        self.code = build(phase)
        self.memory = bytearray(1 << 24)
        for start, buffer in inputs:
            assert start + len(buffer) <= len(self.memory)
            self.memory[start:start+len(buffer)] = buffer
        self.r = [0] * 32
        self.r[2] = len(self.memory)
        self.pc = 0x1000
        self.cycles = self.instructions = 0
        self.oracle = Oracle(zero)
        self.accepted = None
    def access(self, address, width):
        if address % width or address + width > len(self.memory):
            raise AssertionError(('memory access', hex(self.pc), hex(address), width))
    def execute(self, limit=30_000_000):
        r, mem, words = self.r, self.memory, self.code
        for _ in range(limit):
            assert self.pc >= 0x1000 and self.pc % 4 == 0
            w = words[(self.pc - 0x1000) // 4]
            op, rd, f3, a, b = w & 127, (w >> 7) & 31, (w >> 12) & 7, (w >> 15) & 31, (w >> 20) & 31
            imm = signed(w >> 20, 12)
            next_pc = self.pc + 4
            cost = 1
            if op == 0x37: r[rd] = signed(w & 0xfffff000, 32) & MASK
            elif op == 0x13:
                if f3 == 0: r[rd] = (r[a] + imm) & MASK
                elif f3 == 1: r[rd] = (r[a] << ((w >> 20) & 63)) & MASK
                elif f3 == 5:
                    assert w >> 26 == 0
                    r[rd] = r[a] >> ((w >> 20) & 63)
                elif f3 == 4: r[rd] = (r[a] ^ imm) & MASK
                elif f3 == 6: r[rd] = (r[a] | imm) & MASK
                elif f3 == 7: r[rd] = r[a] & (imm & MASK)
                else: raise AssertionError(hex(w))
            elif op == 0x33:
                assert f3 == 0 and w >> 25 in (0, 32)
                r[rd] = (r[a] + r[b] if w >> 25 == 0 else r[a] - r[b]) & MASK
            elif op == 3:
                width = {3: 8, 4: 1}[f3]; address = (r[a] + imm) & MASK
                self.access(address, width)
                r[rd] = int.from_bytes(mem[address:address+width], 'little')
            elif op == 0x23:
                offset = signed(((w >> 25) << 5) | ((w >> 7) & 31), 12)
                width = {3: 8, 0: 1}[f3]; address = (r[a] + offset) & MASK
                self.access(address, width)
                mem[address:address+width] = (r[b] & ((1 << (8 * width)) - 1)).to_bytes(width, 'little')
            elif op == 0x63:
                offset = signed(((w >> 31) << 12) | (((w >> 7) & 1) << 11) | (((w >> 25) & 63) << 5) | (((w >> 8) & 15) << 1), 13)
                assert f3 in (0, 1)
                if (r[a] == r[b]) != bool(f3): next_pc = self.pc + offset
            elif op == 0x6f:
                offset = signed(((w >> 31) << 20) | (((w >> 12) & 255) << 12) | (((w >> 20) & 1) << 11) | (((w >> 21) & 1023) << 1), 21)
                r[rd], next_pc = next_pc, self.pc + offset
            elif op == 0x67:
                assert f3 == 0
                target = (r[a] + imm) & MASK & ~1
                r[rd], next_pc = next_pc, target
            elif w == 0x73:
                if r[5] == 0:
                    self.accepted = r[10] == 1
                    self.cycles += cost; self.instructions += 1
                    return
                assert r[5] == 1 and r[11] % 8 == 0
                source, count, target = r[10], r[11] // 8, r[12]
                assert source % 8 == target % 8 == 0
                assert source + count <= len(mem) and target + 32 <= len(mem)
                data = bytes(mem[source:source+count])
                mem[target:target+32] = self.oracle(data)
                cost = 8 * max(1, (count + 63) // 64)
            else: raise AssertionError(('instruction', hex(w), hex(self.pc)))
            r[0] = 0
            self.pc = next_pc & MASK
            self.cycles += cost
            self.instructions += 1
        if limit == 30_000_000: raise AssertionError('execution did not finish within test limit')
    def buffer(self, address, count): return bytes(self.memory[address:address+count])
    def metrics(self):
        return {'instructions_executed': self.instructions, 'cycles': self.cycles,
                'hash_calls': self.oracle.calls, 'compressions': self.oracle.compressions}

def main():
    secret_key, message = bytes(range(32)), bytes(range(32))
    profile = {}
    h = Oracle(); pk = keygen(h, secret_key)
    machine = Machine('keygen', [(0x20, secret_key)])
    machine.execute()
    assert machine.accepted and machine.buffer(0x40, 16) == pk
    assert machine.buffer(0x60, 1 << 17) == bytes(1 << 17)
    assert machine.oracle.compressions == h.compressions == 761
    changed_key = secret_key[:16] + bytes([secret_key[16] ^ 1]) + secret_key[17:]
    changed_pk = keygen(Oracle(), changed_key)
    changed_machine = Machine('keygen', [(0x20, changed_key)])
    changed_machine.execute()
    assert changed_machine.accepted and changed_machine.buffer(0x40, 16) == changed_pk != pk
    assert query(Oracle(), 6, 0, 0, changed_key + message) != query(Oracle(), 6, 0, 0, secret_key + message)
    profile['keygen'] = machine.metrics()
    print('keygen matches reference:', profile['keygen'], flush=True)
    h = Oracle(); signature = sign(h, secret_key, pk, message)
    assert signature is not None and len(signature) == SIGNATURE_BYTES
    machine = Machine('sign', [(0, message), (0x20, secret_key), (0x40, pk), (0x60, bytes([0xa5]) * (1 << 17))])
    machine.execute()
    assert machine.accepted and machine.buffer(0x20060, SIGNATURE_BYTES) == signature
    assert machine.oracle.compressions == h.compressions == 121008
    assert h.compressions < (1 << 17)
    profile['sign'] = machine.metrics()
    print('sign matches reference:', profile['sign'], flush=True)
    machine = Machine('expand', [(0, message), (0x40, pk), (0x20060, signature)])
    machine.execute()
    assert machine.accepted and machine.buffer(WITNESS_BASE, SIGNATURE_BYTES) == signature
    assert machine.oracle.calls == 0
    profile['expand'] = machine.metrics()
    print('expand preserves signature:', profile['expand'], flush=True)
    h = Oracle(); assert verify(h, pk, message, signature)
    machine = Machine('verify', [(0, message), (0x40, pk), (WITNESS_BASE, signature)])
    machine.execute()
    assert machine.accepted and machine.oracle.compressions == h.compressions
    profile['verify'] = machine.metrics()
    print('verify matches reference:', profile['verify'], flush=True)
    damaged = bytearray(signature); damaged[-1] ^= 1
    assert not verify(Oracle(), pk, message, damaged)
    machine = Machine('verify', [(0, message), (0x40, pk), (WITNESS_BASE, damaged)])
    machine.execute(); assert not machine.accepted
    assert not verify(Oracle(), pk, bytes(reversed(message)), signature)
    changed_randomizer = bytearray(signature); changed_randomizer[0] ^= 1
    assert not verify(Oracle(), pk, message, changed_randomizer)
    machine = Machine('verify', [(0, message), (0x40, pk), (WITNESS_BASE, changed_randomizer)])
    machine.execute(); assert not machine.accepted
    assert signature[:RANDOMIZER_BYTES] == query(Oracle(), 6, 0, 0, secret_key + message)
    print('modified signature, randomizer, and wrong message rejected', flush=True)
    path = Path(__file__).with_name('measured-run.json')
    path.write_text(json.dumps({'test_only': True, 'oracle': 'SHA-256', 'signature_bytes': SIGNATURE_BYTES,
        'public_key': pk.hex(), 'signature_sha256': hashlib.sha256(signature).hexdigest(), 'phases': profile}, indent=2) + '\n')

if __name__ == '__main__': main()
