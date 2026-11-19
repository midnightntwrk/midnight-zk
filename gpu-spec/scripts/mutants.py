#!/usr/bin/env python3
# This file is part of MIDNIGHT-ZK.
# Copyright (C) Midnight Foundation
# SPDX-License-Identifier: Apache-2.0
# Licensed under the Apache License, Version 2.0 (the "License");
# You may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
"""Mutation run of the oracle.

Each mutant is one small wrong change to a definition. A mutant is killed
when `lake build --wfail` fails (a theorem, a pin or a guard breaks), when
`scripts/check_vectors.sh` fails (a golden vector changes), or when the replay
of the saved Quint traces disagrees. Mutant 00 changes nothing and must
survive: it shows that a kill is not an accident of the environment. A
survivor fails the run unless RESULTS.md gives its equivalence argument
(`EQUIVALENT` below).

Usage: mutants.py COPY [ID ...]
COPY is a scratch copy of gpu-spec/ with a built oracle and with the traces of
`scripts/quint_check.sh` under quint/traces (the script edits files in COPY and
restores them; never run it on the work tree). Exit 1 on an unexpected
survivor or a mutant whose text no longer matches the source."""
import subprocess,sys,os,shutil
if len(sys.argv) < 2:
    sys.exit(__doc__)
G=os.path.abspath(sys.argv[1]); R=G+'/oracle'
EQUIVALENT={'47'}
Sv='GpuSpec/Service.lean'
M=[
('00 null-control','GpuSpec/Field.lean',"def blsGen : Nat := 7","def blsGen : Nat := 7 "),
# the 19 mutants of the phase-1 run, on the new text
('01 fft-hi-add','GpuSpec/Ntt.lean',"let hi := (e.zip tw).map fun (x, t) => subM p x t","let hi := (e.zip tw).map fun (x, t) => addM p x t"),
('02 msm-skip-digit1','GpuSpec/Msm.lean',"((buckets.drop 1).reverse","((buckets.drop 2).reverse"),
('03 admit-offbyone',Sv,"if need ≤ free0 then onDevice s stepGpu need free0","if need ≤ free0 + 1 then onDevice s stepGpu need free0"),
('04 readback-noop',Sv,"| 4 => readback s (argA op)","| 4 => s"),
('05 readback-allow4',Sv,"c = 4 && argA op > 3","c = 4 && argA op > 4"),
('06 wipe-keeps-dirty',Sv,"wipeOk := true, dirty := false,","wipeOk := true, dirty := s.dirty,"),
('07 reply-skip-verify',Sv,"  else if !s.verifyOk then\n    -- GPU-040","  else if false then\n    -- GPU-040"),
('08 restart-le',Sv,"if r.length < s.limit then","if r.length ≤ s.limit then"),
('09 rot-no-ratio','GpuSpec/Quotient.lean',"rot * (cs.ratio : Int)","rot"),
('10 fault-nocount',Sv,"{ s with fallbacks := s.fallbacks + 1, degraded := true,                 -- GPU-012","{ s with degraded := true,"),
('11 lease-keeps-work',Sv,"{ s with devWork := false, leaseLost := true, lockHeld := false,","{ s with leaseLost := true, lockHeld := false,"),
('12 intt-no-ninv','GpuSpec/Ntt.lean',"(ntt p (invM p ω) a).map (mulM p ninv)","(ntt p (invM p ω) a)"),
('13 horner-both','GpuSpec/Quotient.lean',None,None),
('14 evict-keeps-ondev',Sv,"onDev := (st == stepGpu || st == stepWait),","onDev := (st == stepGpu || st == stepWait || st == stepEvict),"),
('15 wipefail-stays-up',Sv,"recordFailures (1 + s.waiting)\n      { (gone s) with errors := s.errors + 1, clientCpu := s.clientCpu + 1 + s.waiting }","afterReply { (endRequest s) with errors := s.errors + 1, clientCpu := s.clientCpu + 1 } s.overBound 1"),
('16 bench-noflag',Sv,"runFailed := s.runFailed || (s.bench && deg),","runFailed := s.runFailed,"),
('17 degraded-evict-unmarked',Sv,"degraded := st == stepEvict }","degraded := false }"),
('18 msm-ref-wrong','GpuSpec/Msm.lean',"def msm (p : Nat) (s g : List Nat) : Nat := msmRaw s g % p","def msm (p : Nat) (s g : List Nat) : Nat := (msmRaw s g + s.length) % p"),
('19 mask-ident','GpuSpec/Msm.lean',"subM p (msm p (maskScalars p s r) g) (msm p r g)","msm p s g"),
# new definitions
('20 breaker-window-lt',Sv,"!decide (s.brWindow ≤ s.clock - t)","!decide (s.brWindow < s.clock - t)"),
('21 breaker-no-cooldown',Sv,"{ s with brFails := [], brOpenUntil := s.clock + s.brCooldown }","{ s with brFails := [], brOpenUntil := s.clock }"),
('22 breaker-limit-gt',Sv,"if max s.brLimit 1 ≤ kept.length then","if max s.brLimit 1 < kept.length then"),
('23 breaker-open-le',Sv,"decide (s.clock < s.brOpenUntil)","decide (s.clock ≤ s.brOpenUntil)"),
('24 served-keeps-fails',Sv,"brFails := [] }","brFails := s.brFails }"),
('25 absent-no-failure',Sv,"recordFailure { s with clientCpu := s.clientCpu + 1 }","{ s with clientCpu := s.clientCpu + 1 }"),
('26 skip-not-counted',Sv,"{ s with clientCpu := s.clientCpu + 1, breakerSkips := s.breakerSkips + 1 }","{ s with clientCpu := s.clientCpu + 1 }"),
('27 acceptance-serves',Sv,"else if s.acceptance && (s.degraded || decide (0 < s.fallbacks)) then","else if false && (s.degraded || decide (0 < s.fallbacks)) then"),
('28 acceptance-evict-runs',Sv,"if s.acceptance then noPhase s stepEvict s.reduced freed s.tables       -- GPU-078\n","if false then noPhase s stepEvict s.reduced freed s.tables\n"),
('29 accepts-not-counted',Sv,"verifyAccepts := s.verifyAccepts + (if s.verifyOk then 1 else 0)","verifyAccepts := s.verifyAccepts"),
('30 bad-readback-not-counted',Sv,"badReadbacks := s.badReadbacks + (if k > 3 then 1 else 0) }","badReadbacks := s.badReadbacks }"),
('31 unverified-not-counted',Sv,"unverifiedReturned := s.unverifiedReturned + (if s.verifyOk then 0 else 1),","unverifiedReturned := s.unverifiedReturned,"),
('32 wipe-keeps-tables',Sv,"onDev := s.onDev && hold, tables := false }","onDev := s.onDev && hold, tables := s.tables && hold }"),
('33 decline-total-only',Sv,"             declines := countAt s.declines r, declined := s.declined + 1 }  -- GPU-073","             declines := s.declines, declined := s.declined + 1 }"),
('34 keep-ignored',Sv,"let hold := s.keep && !s.wsl","let hold := false"),
('35 booth-sign','GpuSpec/Msm.lean',"if wval / 2 ^ c % 2 = 1 then -(((2 ^ c - enc) % 2 ^ c : Nat) : Int) else (enc : Int)","if wval / 2 ^ c % 2 = 1 then (((2 ^ c - enc) % 2 ^ c : Nat) : Int) else (enc : Int)"),
('36 abs-off-by-one','GpuSpec/Msm.lean',"decide (x > (p - 1) / 2)","decide (x > (p - 1) / 2 + 1)"),
('37 booth-nwins','GpuSpec/Msm.lean',"  let nw := (bits - 1) / c + 1\n  (List.range nw).reverse.foldl\n    (fun acc w => addM p (shiftWindow p c acc) (boothWindowSum","  let nw := (bits - 1) / c\n  (List.range nw).reverse.foldl\n    (fun acc w => addM p (shiftWindow p c acc) (boothWindowSum"),
('38 batch-wrong-scalar','GpuSpec/Msm.lean',"addM p acc (mulM p (s.headD 0) b)","addM p acc (mulM p (s.headD 1) b)"),
('39 booth-buckets-short','GpuSpec/Msm.lean',"(List.range' 1 (2 ^ (c - 1))).map fun m => boothBucket","(List.range' 1 (2 ^ (c - 1) - 1)).map fun m => boothBucket"),
('40 tile-drop-last','GpuSpec/Quotient.lean',"(List.range ((n + t - 1) / t)).map (· * t)","(List.range (n / t)).map (· * t)"),
('41 tile-overrun','GpuSpec/Quotient.lean',"(List.range' s (min t (n - s))).map f","(List.range' s t).map f"),
('42 gate-order','GpuSpec/Declines.lean',"  if len < 2 ∨ isPow2 len = false ∨ 2 ^ maxLog < len then some .shape\n  else if len < 2 ^ minK then some .belowMinK\n  else if devicePresent = false then some .noDevice","  if len < 2 ∨ isPow2 len = false ∨ 2 ^ maxLog < len then some .shape\n  else if devicePresent = false then some .noDevice\n  else if len < 2 ^ minK then some .belowMinK"),
('43 gateMsm-le','GpuSpec/Declines.lean',"  if len = 0 ∨ 2 ^ maxLog < len then some .shape\n  else if len < 2 ^ minK then some .belowMinK","  if len = 0 ∨ 2 ^ maxLog < len then some .shape\n  else if len ≤ 2 ^ minK then some .belowMinK"),
('44 shift-any','GpuSpec/Declines.lean',"if powM p zeta 3 = 1 % p ∧ zeta % p ≠ 1 % p then none else some .shape","if powM p zeta 3 = 1 % p then none else some .shape"),
('45 count-skip','GpuSpec/Declines.lean',"    | .decline r => cs.bump c.kind r\n","    | .decline _ => cs\n"),
('46 permit-extended','GpuSpec/DataMove.lean',"  | .baseTransform | .msmPoint | .msmBuckets | .quotientCoeffs | .counter => true","  | .baseTransform | .msmPoint | .msmBuckets | .quotientCoeffs | .counter | .extended => true"),
('47 fft-base-noreduce','GpuSpec/Ntt.lean',"    if a.length ≤ 1 then a.map (· % p)","    if a.length ≤ 1 then a"),
('48 coset-no-scale','GpuSpec/Ntt.lean',None,None),
('49 quotient-no-divide','GpuSpec/Quotient.lean',"mulM p v (invM p (subM p (powM p x n) 1))","mulM p v 1"),
('50 crash-no-failure',Sv,"recordFailures callers { (gone s) with clientCpu := s.clientCpu + callers }","{ (gone s) with clientCpu := s.clientCpu + callers }"),
('51 gateMsm2-no-mismatch','GpuSpec/Declines.lean',"if scalars ≠ bases then some .shape else gateMsm","if false then some .shape else gateMsm"),
('52 fft-makes-extended','GpuSpec/DataMove.lean',"| .fft => if ks = [.baseCoeffs] then some .baseTransform else none","| .fft => if ks = [.baseCoeffs] then some .extended else none"),
('53 coset-mislabelled','GpuSpec/DataMove.lean',"| .cosetExtend => if ks = [.baseCoeffs] then some .extended else none","| .cosetExtend => if ks = [.baseCoeffs] then some .baseTransform else none"),
('54 ctx-at-start',Sv,"\n    dirty := false, ctx := false, devUsed","\n    dirty := false, ctx := true, devUsed"),
('56 os-draw-from-caller','GpuSpec/Hooks.lean',"  | .blind .os =>\n    match r.osRng with","  | .blind .os =>\n    match r.rng with"),
('57 os-draw-uncounted','GpuSpec/Hooks.lean',"drawnOs := r.proof.drawnOs + 1 },","drawnOs := r.proof.drawnOs },"),
('58 expected-decline-is-fallback',Sv,"def fault (s : St) (r : Nat) : St :=\n  if 2 ≤ r then","def fault (s : St) (r : Nat) : St :=\n  if 0 ≤ r then"),
('59 fault-decline-not-fallback',Sv,"def fault (s : St) (r : Nat) : St :=\n  if 2 ≤ r then","def fault (s : St) (r : Nat) : St :=\n  if 3 ≤ r then"),
('60 window0-unbounded',Sv,"  if s.window = 0 then s.restartTimes\n","  if false then s.restartTimes\n"),
('61 free-unzeroed-ok','GpuSpec/DataMove.lean',"    | some x => x.kind == .msmBuckets && x.host && !x.zeroed","    | some x => x.kind == .msmBuckets && x.host && !x.zeroed && false"),
('62 device-ignores-position','GpuSpec/Hooks.lean',None,None),
('63 inst-column-zero','GpuSpec/Quotient.lean',"colAt cs.inst c (rotIndex cs i r)","colAt cs.inst 0 (rotIndex cs i r)"),
('64 vanishing-exponent','GpuSpec/Quotient.lean',"subM p (powM p x n) 1","subM p (powM p x (num.length / n)) 1"),
('65 counter-read-any-phase',Sv,"(argA op == 2 && s.phase == proved)","(argA op == 2)"),
('66 host-reads-zeroed','GpuSpec/DataMove.lean',None,None),
('67 challenge-lookup','GpuSpec/Quotient.lean',"cs.challenges.getD k 0 % p","cs.challenges.getD (k % 2) 0 % p"),
('55 gate-shape-pow2','GpuSpec/Declines.lean',"if len < 2 ∨ isPow2 len = false ∨ 2 ^ maxLog < len then some .shape","if len < 2 ∨ 2 ^ maxLog < len then some .shape"),
]
only=sys.argv[2:]
unexpected=[]
for name,f,a,b in M:
    if only and name.split()[0] not in only: continue
    p=R+'/'+f; src=open(p).read()
    if name.startswith('13'):
        new=src.replace("addM p (mulM p acc y) (evalE p cs i g)","addM p acc (mulM p y (evalE p cs i g))").replace("addM p (mulM p acc y) ((exec p cs i pr []).headD 0)","addM p acc (mulM p y ((exec p cs i pr []).headD 0))")
    elif name.startswith('62'):
        a='match r.osRng with'; new=src.replace('| .blind .os =>\n    match r.osRng with','| .blind .os =>\n    match r.osRng with',1)
        import re
        m=re.search(r'fallbacks := r.fallbacks \+ \(if \(dev r.pos c\).isSome then 0 else 1\)',src)
        new=src.replace('(dev r.pos c)','(dev 0 c)') if '(dev r.pos c)' in src else src
    elif name.startswith('66'):
        import re
        m=re.search(r'def hostReadable[^\n]*\n(?:.*\n)*?\n',src); body=m.group(0)
        new=src.replace(body,body.replace('!x.zeroed','true').replace('x.zeroed == false','true').replace('x.zeroed = false','True'))
    elif name.startswith('48'):
        a="evalPoly p a (mulM p ζ (powM p ωe k))"; assert src.count(a)==1; new=src.replace(a,"evalPoly p a (powM p ωe k)")
    else:
        if src.count(a)!=1: print(name,'SETUP-ERROR count',src.count(a),flush=True); unexpected.append(name); continue
        new=src.replace(a,b)
    if new==src and not name.startswith('00'): print(name,'SETUP-ERROR nochange',flush=True); continue
    open(p,'w').write(new)
    env=dict(os.environ,LEAN_ABORT_ON_PANIC='1')
    import signal
    pr=subprocess.Popen(['lake','build','--wfail'],cwd=R,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,env=env,start_new_session=True)
    errs=[]
    for line in pr.stdout:
        if line.startswith('error'):
            errs.append(line.strip())
            try: os.killpg(pr.pid,signal.SIGKILL)   # first error is a kill: stop the build
            except ProcessLookupError: pass
            break
    pr.wait()
    res='KILLED-BUILD' if (errs or pr.returncode) else None
    if not res:
        v=subprocess.run(['bash','scripts/check_vectors.sh'],cwd=G,capture_output=True,text=True,env=env)
        res='KILLED-VECTORS' if v.returncode else None
    if not res:
        tr=G+'/quint/traces'; bad=False
        for inst in sorted(os.listdir(tr)):
            q=subprocess.run(['python3','-I',G+'/scripts/quint_replay.py','--oracle',R+'/.lake/build/bin/oracle','--traces',tr+'/'+inst,'--op-var','lastOp','--compare','s','--drop','prev'],capture_output=True,text=True,env=env)
            if q.returncode: bad=True; break
        res='KILLED-QUINT' if bad else 'SURVIVES'
    print(name,res,'|',' ;; '.join(e[:110] for e in errs),flush=True)
    i=name.split()[0]
    if (res=='SURVIVES') != (i=='00' or i in EQUIVALENT): unexpected.append(name)
    open(p,'w').write(src)
print('done; unexpected:',unexpected)
sys.exit(1 if unexpected else 0)
