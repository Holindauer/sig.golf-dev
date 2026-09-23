import sys, random, json
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
from build import Assembler,HASH,LEVEL,LEAF,CHAIN,STEP,INDEX0,INDEX1,INDEX2
from check import Machine
old=Assembler();old.header(2,leaf=True,chain=True,step=True); original=old.finish()
a=Assembler();a.li(28,HASH);a.li(10,2)
for source,shift in [(LEVEL,8),(LEAF,16),(CHAIN,24),(STEP,32)]:
 a.ld(11,28,source-HASH);a.shift(11,11,shift);a.add(10,10,11)
a.store(10,28)
for offset,source in [(8,INDEX0),(16,INDEX1),(24,INDEX2)]:
 a.ld(11,28,source-HASH);a.store(11,28,offset)
a.i(0x13,0,28,28,24);a.jump('end');executed=len(a.words)
while len(a.words)<len(original):a.i(0x13,0,0,0,0)
a.label('end');optimized=a.finish();rng=random.Random(4096)
for _ in range(30):
 memory=rng.randbytes(0x80600);regs=[0]+[rng.getrandbits(64) for i in range(31)];states=[]
 for code,steps in [(original,len(original)),(optimized,executed)]:
  m=Machine('verify',[]);m.code=code;m.memory[:len(memory)]=memory;m.r=regs.copy();m.execute(limit=steps);states.append(m)
 x,y=states;assert x.r==y.r and x.memory==y.memory and x.pc==y.pc
print(json.dumps({'cases':30,'original_steps':len(original),'optimized_steps':executed,'saved_per_chain_hash':len(original)-executed,'status':'differential tests only; see FastChainHeader.lean and the full build for formal validation'}))
