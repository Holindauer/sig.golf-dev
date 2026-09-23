"""Differential state checks for the experimental fixed-layout copy replacement."""
import random
from build import Assembler
from check import Machine

rng = random.Random(20260923)
checked = 0
for source in [0x40, 0x80300, 0x80510]:
    for destination in [source-8, source, source+8, source+16, 0x80020]:
        for _ in range(4):
            old = Assembler(); old.copy(source, destination)
            new = Assembler(); new.optimize_copy16 = True; new.copy(source, destination)
            original, optimized = old.finish(), new.finish()
            assert len(original) == len(optimized)
            # Two loop iterations cost six instructions each; the replacement skips padding.
            old_steps = len(original) + 6
            new_steps = len(optimized) - 1
            seed = rng.randbytes(0x80600)
            regs = [0] + [rng.getrandbits(64) for _ in range(31)]
            states=[]
            for code, steps in [(original,old_steps),(optimized,new_steps)]:
                m=Machine('verify',[]);m.code=code;m.memory[:len(seed)]=seed;m.r=regs.copy()
                m.execute(limit=steps)
                states.append(m)
            a,b=states
            assert a.r==b.r and a.memory==b.memory and a.pc==b.pc
            assert a.pc==0x1000+4*len(original)
            assert a.cycles-b.cycles==7
            checked+=1
print(f'{checked} copy-state cases passed, including overlapping buffers; 7 cycles saved per copy.')
