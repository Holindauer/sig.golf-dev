"""Generate a deterministic binary hypertree candidate. No security certificate is claimed."""
from pathlib import Path

HEIGHT = 160
CHAINS = 46
RANDOMIZER_BYTES = 32
SIGNATURE_BYTES = RANDOMIZER_BYTES + 32 + (HEIGHT - 1) * (16 * CHAINS + 16)
WITNESS_BASE = 0x20060 + SIGNATURE_BYTES
HASH = 0x80000
ANSWER = 0x80300
LEVEL, INDEX0, INDEX1, INDEX2, SELECTOR, LEAF, CHAIN, STEP, MODE, POINTER = range(0x80400, 0x80450, 8)
CURRENT, VALUE, PUB0, PUB1 = 0x80500, 0x80510, 0x80520, 0x80530
DIGITS, ENDPOINTS = 0x80600, 0x80800

class Assembler:
    def __init__(self):
        self.words, self.labels, self.fixups = [], {}, []
        self.serial = 0
        self.optimize_copy16 = False
        self.optimize_chain_header = False
        self.optimize_address_reuse = False
        self.optimize_only_chain = False
    def emit(self, w): self.words.append(w & 0xffffffff)
    def label(self, name):
        assert name not in self.labels, name
        self.labels[name] = 4 * len(self.words)
    def fresh(self, stem):
        self.serial += 1
        return f'{stem}_{self.serial}'
    def i(self, op, f3, rd, rs, imm):
        assert -2048 <= imm < 2048
        self.emit(((imm & 4095) << 20) | (rs << 15) | (f3 << 12) | (rd << 7) | op)
    def li(self, rd, value):
        if -2048 <= value < 2048: self.i(0x13, 0, rd, 0, value)
        else:
            high = (value + 2048) >> 12
            self.emit((high << 12) | (rd << 7) | 0x37)
            self.i(0x13, 0, rd, rd, value - (high << 12))
    def add(self, rd, a, b): self.emit((b << 20) | (a << 15) | (rd << 7) | 0x33)
    def ori(self, rd, rs, imm): self.i(0x13, 6, rd, rs, imm)
    def andi(self, rd, rs, imm): self.i(0x13, 7, rd, rs, imm)
    def shift(self, rd, rs, n, right=False): self.i(0x13, 5 if right else 1, rd, rs, n)
    def ld(self, rd, rs, off=0): self.i(3, 3, rd, rs, off)
    def lbu(self, rd, rs, off=0): self.i(3, 4, rd, rs, off)
    def store(self, rs, base, off=0, byte=False):
        assert -2048 <= off < 2048
        imm = off & 4095
        self.emit(((imm >> 5) << 25) | (rs << 20) | (base << 15) | ((0 if byte else 3) << 12) | ((imm & 31) << 7) | 0x23)
    def load(self, rd, address): self.li(28, address); self.ld(rd, 28)
    def save(self, rs, address): self.li(28, address); self.store(rs, 28)
    def set(self, address, value): self.li(6, value); self.save(6, address)
    def branch(self, a, b, label, unequal=False):
        self.fixups.append((len(self.words), 'branch', (a, b, unequal), label)); self.emit(0)
    def jump(self, label, link=0):
        self.fixups.append((len(self.words), 'jump', link, label)); self.emit(0)
    def call(self, label): self.jump(label, 1)
    def enter(self, label):
        self.label(label); self.i(0x13, 0, 2, 2, -16); self.store(1, 2)
    def ret(self):
        self.ld(1, 2); self.i(0x13, 0, 2, 2, 16); self.i(0x67, 0, 0, 1, 0)
    def halt(self, accepted): self.li(5, 0); self.li(10, int(accepted)); self.emit(0x73)
    def copy(self, source, destination, count=16):
        assert count % 8 == 0
        if (self.optimize_address_reuse and count == 16 and source == ANSWER and destination == VALUE
                and 'chain_step' in self.labels and 'chain_end' not in self.labels):
            start=len(self.words);
            self.i(0x13,0,28,28,1056);self.i(0x13,0,6,6,1);self.store(6,28)
            self.jump('cached_chain_check')
            self.i(0x13,0,0,0,0)
            self.label('restore_chain_value')
            self.ld(11,28,-1048);self.store(11,28,216);self.ld(11,28,-1040);self.store(11,28,224);self.jump('chain_end')
            while len(self.words)-start<19:self.i(0x13,0,0,0,0)
            return
        if (self.optimize_address_reuse and count==16 and source==VALUE and destination==HASH+32 and 'chain_step' in self.labels and 'chain_end' not in self.labels):
            start=len(self.words);
            self.ld(11,28,source-STEP);self.store(11,28,-1048);self.ld(11,28,source-STEP+8);self.store(11,28,-1040)
            self.li(10,2)
            for src,shift in [(LEVEL,8),(LEAF,16),(CHAIN,24),(STEP,32)]:
                self.ld(11,28,src-STEP);self.shift(11,11,shift);self.add(10,10,11)
            self.store(10,28,-1080)
            for off,src in [(8,INDEX0),(16,INDEX1),(24,INDEX2)]:self.ld(11,28,src-STEP);self.store(11,28,off-1080)
            self.i(0x13,0,28,28,-1056);self.i(0x13,0,10,28,-24);self.li(11,48);self.i(0x13,0,12,28,8);self.li(5,1)
            self.li(13,1);self.shift(13,13,32)
            end=self.fresh('fused_end');self.jump(end)
            self.label('cached_chain_check')
            self.branch(6,7,'restore_chain_value')
            self.ld(10,28,-1080);self.add(10,10,13);self.store(10,28,-1080)
            self.i(0x13,0,28,28,-1056);self.i(0x13,0,10,28,-24);self.jump(end)
            while len(self.words)-start<59:self.i(0x13,0,0,0,0)
            self.label(end);self.fused_hash_ready=True
            return
        if (self.optimize_address_reuse and count == 16
                and 'chain_step' in self.labels and 'chain_end' not in self.labels):
            start = len(self.words)
            self.emit((128 << 12) | (28 << 7) | 0x37)
            self.ld(11,28,source-HASH); self.store(11,28,destination-HASH)
            self.ld(11,28,source-HASH+8); self.store(11,28,destination-HASH+8)
            end = self.fresh('copy6_end'); self.jump(end)
            while len(self.words)-start < 11: self.i(0x13,0,0,0,0)
            self.label(end)
            return
        if self.optimize_copy16 and count == 16 and (not self.optimize_only_chain or ('chain_step' in self.labels and 'chain_end' not in self.labels)):
            # Preserve every final register, the copied memory, and following PCs.
            # Initialize pointers at their final values and address the two words backwards.
            start = len(self.words)
            old_size = (1 if -2048 <= source < 2048 else 2) + (1 if -2048 <= destination < 2048 else 2) + 7
            self.li(6, source + 16)
            if self.optimize_address_reuse:
                self.i(0x13, 0, 7, 6, destination-source)
            else:
                self.li(7, destination + 16)
            self.li(10, 0)
            self.ld(11, 6, -16); self.store(11, 7, -16)
            self.ld(11, 6, -8); self.store(11, 7, -8)
            end = self.fresh('fast_copy_end')
            self.jump(end)
            assert len(self.words) - start <= old_size
            while len(self.words) - start < old_size:
                self.i(0x13, 0, 0, 0, 0)
            self.label(end)
            return
        self.li(6, source); self.li(7, destination); self.li(10, count // 8)
        loop = self.fresh('copy'); self.label(loop)
        self.ld(11, 6); self.store(11, 7)
        self.i(0x13, 0, 6, 6, 8); self.i(0x13, 0, 7, 7, 8); self.i(0x13, 0, 10, 10, -1)
        self.branch(10, 0, loop, True)
    def header(self, tag, leaf=False, chain=False, step=False, message=False):
        if (self.optimize_chain_header and tag == 2 and leaf and chain and step and not message
                and 'chain_step' in self.labels and 'chain_end' not in self.labels):
            start = len(self.words)
            self.li(28, HASH); self.li(10, 2)
            for source, shift in [(LEVEL,8),(LEAF,16),(CHAIN,24),(STEP,32)]:
                self.ld(11,28,source-HASH); self.shift(11,11,shift); self.add(10,10,11)
            self.store(10,28)
            for offset,source in [(8,INDEX0),(16,INDEX1),(24,INDEX2)]:
                self.ld(11,28,source-HASH); self.store(11,28,offset)
            self.i(0x13,0,28,28,24)
            end = self.fresh('fast_header_end'); self.jump(end)
            while len(self.words)-start < 42: self.i(0x13,0,0,0,0)
            self.label(end)
            return
        self.li(10, tag)
        if not message:
            for address, shift in [(LEVEL, 8)] + ([(LEAF, 16)] if leaf else []) + ([(CHAIN, 24)] if chain else []) + ([(STEP, 32)] if step else []):
                self.load(11, address); self.shift(11, 11, shift); self.add(10, 10, 11)
        self.save(10, HASH)
        for offset, source in [(8, INDEX0), (16, INDEX1), (24, INDEX2)]:
            if message: self.li(11, 0)
            else: self.load(11, source)
            self.save(11, HASH + offset)
    def hash_length(self, size):
        # Keep the former two-instruction leaf length setup and all code addresses.
        if size == 768:
            self.emit((11 << 7) | 0x37)
            self.i(0x13, 0, 11, 11, size)
        else:
            self.li(11, size)

    def hash(self, tag, size, **fields):
        if getattr(self, "fused_hash_ready", False):
            assert tag == 2 and size == 48 and fields == dict(leaf=True, chain=True, step=True)
            self.fused_hash_ready = False; self.emit(0x73)
            return
        if (self.optimize_address_reuse and tag == 2 and size == 48
                and fields == dict(leaf=True, chain=True, step=True)
                and 'chain_step' in self.labels and 'chain_end' not in self.labels):
            start = len(self.words)
            self.emit((128 << 12) | (28 << 7) | 0x37)
            self.li(10, 2)
            for source, shift in [(LEVEL,8),(LEAF,16),(CHAIN,24),(STEP,32)]:
                self.ld(11,28,source-HASH); self.shift(11,11,shift); self.add(10,10,11)
            self.store(10,28)
            for offset,source in [(8,INDEX0),(16,INDEX1),(24,INDEX2)]:
                self.ld(11,28,source-HASH); self.store(11,28,offset)
            self.i(0x13,0,28,28,24)
            self.i(0x13,0,10,28,-24); self.li(11,48)
            self.i(0x13,0,12,28,744); self.li(5,1)
            end = self.fresh('reuse_header_end'); self.jump(end)
            while len(self.words)-start < 48: self.i(0x13,0,0,0,0)
            self.label(end); self.emit(0x73)
            return
        self.header(tag, **fields)
        self.li(10, HASH); self.hash_length(size); self.li(12, ANSWER); self.li(5, 1); self.emit(0x73)
    def finish(self):
        for pos, kind, args, label in self.fixups:
            offset = self.labels[label] - 4 * pos
            assert offset % 4 == 0
            if kind == 'branch':
                assert -4096 <= offset < 4096, (label, offset)
                a, b, unequal = args; u = offset & 8191
                self.words[pos] = (((u >> 12) & 1) << 31) | (((u >> 5) & 63) << 25) | (b << 20) | (a << 15) | (int(unequal) << 12) | (((u >> 1) & 15) << 8) | (((u >> 11) & 1) << 7) | 0x63
            else:
                assert -(1 << 20) <= offset < (1 << 20)
                u = offset & 0x1fffff
                self.words[pos] = (((u >> 20) & 1) << 31) | (((u >> 1) & 1023) << 21) | (((u >> 11) & 1) << 20) | (((u >> 12) & 255) << 12) | (args << 7) | 0x6f
        return self.words

def message_index(a, verifying):
    randomizer = WITNESS_BASE if verifying else 0x20060
    if not verifying:
        a.copy(0x20, HASH + 32, 32); a.copy(0, HASH + 64, 32)
        a.hash(6, 96, message=True)
        a.copy(ANSWER, randomizer, RANDOMIZER_BYTES)
    a.copy(0x40, HASH + 32); a.copy(0, HASH + 48, 32)
    a.copy(randomizer, HASH + 80, RANDOMIZER_BYTES)
    a.hash(5, 112, message=True)
    a.copy(ANSWER, INDEX0, 16)
    a.load(6, ANSWER + 16); a.shift(6, 6, 32); a.shift(6, 6, 32, True); a.save(6, INDEX2)

def shift_index(a):
    a.load(6, INDEX0); a.load(7, INDEX1); a.load(10, INDEX2)
    a.andi(11, 6, 1); a.save(11, SELECTOR)
    a.shift(6, 6, 1, True); a.shift(11, 7, 63); a.add(6, 6, 11); a.save(6, INDEX0)
    a.shift(7, 7, 1, True); a.shift(11, 10, 63); a.add(7, 7, 11); a.save(7, INDEX1)
    a.shift(10, 10, 1, True); a.save(10, INDEX2)

def encode(a):
    a.enter('encode')
    a.load(6, CURRENT); a.load(7, CURRENT + 8); a.li(10, DIGITS); a.li(11, 43); a.li(12, 301)
    a.label('digits_loop')
    a.andi(13, 6, 7); a.store(13, 10, byte=True)
    # SUB checksum, checksum, digit.
    a.emit((0x20 << 25) | (13 << 20) | (12 << 15) | (12 << 7) | 0x33)
    a.shift(6, 6, 3, True); a.shift(13, 7, 61); a.add(6, 6, 13); a.shift(7, 7, 3, True)
    a.i(0x13, 0, 10, 10, 1); a.i(0x13, 0, 11, 11, -1); a.branch(11, 0, 'digits_loop', True)
    for offset in range(3):
        a.andi(13, 12, 7); a.store(13, 10, offset, byte=True); a.shift(12, 12, 3, True)
    a.ret()

def save_public(a):
    a.load(6, LEAF); a.shift(6, 6, 4); a.li(7, PUB0); a.add(7, 7, 6)
    a.load(10, ANSWER); a.load(11, ANSWER + 8); a.store(10, 7); a.store(11, 7, 8)

def capture(a, bottom=False):
    skip = a.fresh('no_capture')
    a.load(6, MODE); a.branch(6, 0, skip)
    a.load(6, LEAF); a.load(7, SELECTOR); a.branch(6, 7, skip, True)
    a.load(7, POINTER)
    if not bottom:
        a.load(6, CHAIN); a.li(10, DIGITS); a.add(10, 10, 6); a.lbu(10, 10)
        a.load(11, STEP); a.branch(10, 11, skip, True)
        a.shift(6, 6, 4); a.add(7, 7, 6)
    a.load(10, VALUE); a.load(11, VALUE + 8); a.store(10, 7); a.store(11, 7, 8)
    a.label(skip)

def leaf_functions(a, verifying):
    a.enter('leaf')
    a.set(CHAIN, 0); a.set(STEP, 0)
    a.load(6, LEVEL); a.branch(6, 0, 'bottom_leaf')
    a.label('chain_loop')
    if verifying:
        a.load(6, CHAIN); a.load(7, POINTER); a.shift(10, 6, 4); a.add(7, 7, 10)
        a.ld(10, 7); a.ld(11, 7, 8); a.save(10, VALUE); a.save(11, VALUE + 8)
        a.li(7, DIGITS); a.add(7, 7, 6); a.lbu(10, 7); a.save(10, STEP)
    else:
        a.copy(0x20, HASH + 32, 32); a.hash(1, 64, leaf=True, chain=True); a.copy(ANSWER, VALUE)
        a.set(STEP, 0)
    a.label('chain_step')
    if not verifying: capture(a)
    if verifying:
        a.li(28, STEP); a.label('chain_step_reuse'); a.ld(6,28)
    else: a.load(6, STEP)
    a.li(7, 7); a.branch(6, 7, 'chain_end')
    a.copy(VALUE, HASH + 32); a.hash(2, 48, leaf=True, chain=True, step=True); a.copy(ANSWER, VALUE)
    if not verifying:
        a.load(6, STEP); a.i(0x13, 0, 6, 6, 1); a.save(6, STEP); a.jump('chain_step')
    a.label('chain_end')
    a.load(6, CHAIN); a.shift(7, 6, 4); a.li(10, ENDPOINTS); a.add(7, 7, 10)
    a.load(10, VALUE); a.load(11, VALUE + 8); a.store(10, 7); a.store(11, 7, 8)
    a.i(0x13, 0, 6, 6, 1); a.save(6, CHAIN); a.li(7, CHAINS); a.branch(6, 7, 'chain_loop', True)
    a.copy(ENDPOINTS, HASH + 32, 16 * CHAINS); a.hash(3, 32 + 16 * CHAINS, leaf=True)
    save_public(a); a.ret()
    a.label('bottom_leaf')
    if verifying:
        a.load(7, POINTER); a.ld(10, 7); a.ld(11, 7, 8); a.save(10, VALUE); a.save(11, VALUE + 8)
    else:
        a.copy(0x20, HASH + 32, 32); a.hash(1, 64, leaf=True, chain=True); a.copy(ANSWER, VALUE)
        capture(a, bottom=True)
    a.copy(VALUE, HASH + 32); a.hash(2, 48, leaf=True, chain=True, step=True)
    save_public(a); a.ret()

def tree_function(a, verifying):
    a.enter('tree')
    if verifying:
        a.load(6, SELECTOR); a.save(6, LEAF); a.call('leaf')
    else:
        a.set(LEAF, 0); a.call('leaf'); a.set(LEAF, 1); a.call('leaf')
    done = a.fresh('sibling_done')
    if not verifying:
        a.load(6, MODE); a.branch(6, 0, done)
    a.load(6, SELECTOR); a.i(0x13, 4, 6, 6, 1); a.shift(6, 6, 4); a.li(7, PUB0); a.add(7, 7, 6)
    a.load(10, POINTER); a.load(11, LEVEL)
    small = a.fresh('small_sibling'); ready = a.fresh('sibling_ready')
    a.branch(11, 0, small); a.i(0x13, 0, 10, 10, 16 * CHAINS); a.jump(ready)
    a.label(small); a.i(0x13, 0, 10, 10, 16); a.label(ready)
    if verifying:
        a.ld(11, 10); a.ld(12, 10, 8); a.store(11, 7); a.store(12, 7, 8)
    else:
        a.ld(11, 7); a.ld(12, 7, 8); a.store(11, 10); a.store(12, 10, 8)
    a.label(done)
    a.copy(PUB0, HASH + 32, 32); a.hash(4, 64); a.copy(ANSWER, CURRENT); a.ret()

def build(phase):
    a = Assembler()
    if phase == 'expand':
        a.copy(0x20060, WITNESS_BASE, SIGNATURE_BYTES); a.halt(True); return a.finish()
    verifying = phase == 'verify'
    a.optimize_copy16 = verifying
    a.optimize_chain_header = verifying
    a.optimize_address_reuse = verifying
    a.optimize_only_chain = True
    if phase == 'keygen':
        a.set(LEVEL, HEIGHT - 1); a.call('tree'); a.copy(CURRENT, 0x40); a.halt(True)
    else:
        a.set(MODE, 0 if verifying else 1); a.set(POINTER, (WITNESS_BASE if verifying else 0x20060) + RANDOMIZER_BYTES)
        message_index(a, verifying)
        a.label('layer_loop'); shift_index(a)
        a.load(6, LEVEL); a.branch(6, 0, 'encoded'); a.call('encode'); a.label('encoded'); a.call('tree')
        a.load(6, LEVEL); a.load(7, POINTER); a.branch(6, 0, 'short_layer')
        a.i(0x13, 0, 7, 7, 16 * CHAINS + 16); a.jump('advanced')
        a.label('short_layer'); a.i(0x13, 0, 7, 7, 32); a.label('advanced'); a.save(7, POINTER)
        a.i(0x13, 0, 6, 6, 1); a.save(6, LEVEL); a.li(7, HEIGHT); a.branch(6, 7, 'layer_loop', True)
        for offset in (0, 8):
            a.load(6, CURRENT + offset); a.load(7, 0x40 + offset); a.branch(6, 7, 'reject', True)
        a.halt(True); a.label('reject'); a.halt(False)
    if phase != 'keygen': encode(a)
    tree_function(a, verifying); leaf_functions(a, verifying)
    return a.finish()

def generate():
    root = Path(__file__).resolve().parents[2]
    path = root / 'SigGolfCandidate/Hypertree/Images.lean'
    lines = ['-- Generated by examples/hypertree/build.py.', 'import SigGolf', '', 'namespace SigGolfCandidate.Hypertree', 'open SigGolf', '', f'def signatureBytes : Nat := {SIGNATURE_BYTES}', '']
    for phase in ['keygen', 'sign', 'expand', 'verify']:
        words = build(phase)
        lines += [f'def {phase} : Riscv.Image where', '  code := [']
        lines += ['    ' + ', '.join(f'0x{w:08x}' for w in words[i:i+8]) + (',' if i + 8 < len(words) else ']') for i in range(0, len(words), 8)]
        lines += ['  data := []', '']
        print(f'{phase}: {len(words)} instructions, {len(words)*4} bytes')
    lines += ['def submission : Submission where', '  sizes := ⟨signatureBytes, signatureBytes⟩', '  layout := Riscv.standardLayout ⟨signatureBytes, signatureBytes⟩', '  image', '    | .keygen => keygen', '    | .sign => sign', '    | .expand => expand', '    | .verify => verify', '', 'end SigGolfCandidate.Hypertree', '']
    path.write_text('\n'.join(lines))

if __name__ == '__main__': generate()
