"""Generate kernel-checked abstract-state checkpoints for the exact keygen image.

This script is not trusted. Each generated runPrefix equation is proved with
Lean's kernel evaluator against Images.lean and the protected interpreter.
Regenerate with: python3 examples/hypertree/keygen_resources.py
"""
from pathlib import Path
import importlib.util
import copy
ROOT = str(Path(__file__).resolve().parents[2])
spec=importlib.util.spec_from_file_location('candidatebuild',ROOT+'/examples/hypertree/build.py')
b=importlib.util.module_from_spec(spec);spec.loader.exec_module(b)
code=b.build('keygen')
mask=(1<<64)-1
s={'pc':0x1000,'regs':[(2,1<<24)],'mem':[(0x80408,0),(0x80410,0),(0x80418,0),(0x80440,0)]}
def get(key,items):
 return next((v for k,v in items if key==k),None)
def reg(r):return 0 if r==0 else get(r,s['regs'])
def update(key,v,field):
 s[field]=([] if v is None else [(key,v&mask)])+[(k,w) for k,w in s[field] if k!=key]
def se(n,w):return n-(1<<w) if n>>(w-1) else n
def binary(f,a,b):return None if a is None or b is None else f(a,b)&mask
def unary(f,a):return None if a is None else f(a)&mask
def valid(p,n):assert p is not None and p+n<=1<<24 and p%n==0,(hex(s['pc']),p,n)
def step():
 pc=s['pc']; w=code[(pc-0x1000)//4];op=w&127;rd=(w>>7)&31;f3=(w>>12)&7;r1=(w>>15)&31;r2=(w>>20)&31;imm=se(w>>20,12)
 s['pc']=pc+4
 if op==0x13:
  f={0:lambda x:x+imm,1:lambda x:x<<((w>>20)&63),5:lambda x:x>>((w>>20)&63),7:lambda x:x&(imm&mask),4:lambda x:x^(imm&mask)}[f3]
  update(rd,unary(f,reg(r1)),'regs')
 elif op==0x33:
  assert f3==0 and w>>25==0
  update(rd,binary(lambda x,y:x+y,reg(r1),reg(r2)),'regs')
 elif op==0x37:update(rd,se(w&0xfffff000,32),'regs')
 elif op==3:
  assert f3==3
  p=binary(lambda x,y:x+y,reg(r1),imm&mask);valid(p,8)
  update(rd,get(p,s['mem']),'regs')
 elif op==0x23:
  assert f3==3
  off=se(((w>>25)<<5)|((w>>7)&31),12)
  p=binary(lambda x,y:x+y,reg(r1),off&mask);valid(p,8)
  update(p,reg(r2),'mem')
 elif op==0x63:
  x,y=reg(r1),reg(r2);assert x is not None and y is not None,(hex(pc),r1,x,r2,y)
  off=se(((w>>31)<<12)|(((w>>7)&1)<<11)|(((w>>25)&63)<<5)|(((w>>8)&15)<<1),13)
  assert f3 in [0,1]
  if (x==y) != bool(f3):s['pc']=(pc+off)&mask
 elif op==0x6f:
  off=se(((w>>31)<<20)|(((w>>12)&255)<<12)|(((w>>20)&1)<<11)|(((w>>21)&1023)<<1),21)
  update(rd,pc+4,'regs');s['pc']=(pc+off)&mask
 elif op==0x67:
  p=reg(r1);assert p is not None
  update(rd,pc+4,'regs');s['pc']=((p+imm)&mask)&~1
 elif op==0x73:
  assert reg(5)==1,(hex(pc),reg(5))
  p,bits,d=reg(10),reg(11),reg(12);assert p%8==0 and p+(bits+7)//8<=1<<24;valid(d,8);assert d+32<=1<<24
  for off in [0,8,16,24]:update(d+off,None,'mem')
  k=max(1,(bits+511)//512);return 8*k,1,k
 else:raise Exception((hex(pc),hex(w)))
 return 1,0,0

def lean_state(name,state):
 def fields(field):return ', '.join(('(.x%d, 0x%x)'%(k,v)) if field=='regs' else ('(0x%x, 0x%x)'%(k,v)) for k,v in state[field])
 return f'def {name} : AbstractState :=\n  ⟨0x{state["pc"]:x}, [{fields("regs")}],\n    [{fields("mem")}]⟩\n'

def generate(chunk=1000,limit=75992):
 states=[copy.deepcopy(s)];summaries=[]
 for start in range(0,limit,chunk):
  count=min(chunk,limit-start);sums=[0,0,0]
  for i in range(count):
   for j,v in enumerate(step()):sums[j]+=v
  states.append(copy.deepcopy(s));summaries.append((count,sums))
 return states,summaries
if __name__=='__main__':
 import sys
 chunk=int(sys.argv[1]) if len(sys.argv)>1 else 1000
 limit=75992
 states,summaries=generate(chunk,limit)
 out=['import SigGolfCandidate.Hypertree.ResourceRun','namespace SigGolfCandidate.Hypertree.KeygenResource','open SigGolfCandidate.Resources SigGolf RiscvZkvm.Rv64','set_option maxRecDepth 10000','set_option maxHeartbeats 0','set_option Elab.async false']
 for i,state in enumerate(states):out.append(lean_state(f'state{i}',state))
 for i,(count,sums) in enumerate(summaries):
  out.append(f'theorem chunk{i} : runPrefix {count} keygen state{i} = some ⟨state{i+1}, {sums[0]}, {sums[1]}, {sums[2]}⟩ := by decide')
 totals=list(map(sum,zip(*(v for _,v in summaries))))
 proof=[f'theorem certifiedPrefix : CertifiedPrefix keygen state0 state{len(summaries)} {limit} {totals[0]} {totals[1]} {totals[2]} := by', '  have h0 := CertifiedPrefix.of_run chunk0']
 for i in range(1,len(summaries)):
  proof.append(f'  have h{i} := h{i-1}.trans (CertifiedPrefix.of_run chunk{i})')
 proof.append(f'  exact h{len(summaries)-1}')
 out.append('\n'.join(proof))
 out.append('end SigGolfCandidate.Hypertree.KeygenResource')
 output = sys.argv[2] if len(sys.argv)>2 else ROOT+'/SigGolfCandidate/Hypertree/KeygenResourceCheckpoints.lean'
 header = "-- Generated abstract-state checkpoints for the exact keygen image.\n-- Every transition is checked by Lean's kernel; the generator is not trusted.\n"
 assert code[(states[-1]['pc']-0x1000)//4] == 0x73 and reg(5) == 0 and reg(10) == 1
 Path(output).write_text(header+'\n\n'.join(out)+'\n')
 print(len(summaries),'chunks',list(map(sum,zip(*(v for _,v in summaries)))),'lastpc',hex(states[-1]['pc']))
