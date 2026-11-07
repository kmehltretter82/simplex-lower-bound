from pathlib import Path
P=Path(__file__).parent
D='.diamond'; B='.bool'; LB=f'(.list {B})'; LLB=f'(.list {LB})'
vars={0:LLB,1:D,2:LB,3:LLB,4:D,5:B,6:LLB,10:D,11:D}
def v(i):return ('v',i)
def c(s,ty):return ('c',s,ty)
def app(t,s,ty=None):return ('app',t,s,ty)
def lam(i,t):return ('lam',i,t)
def brace(t):return ('brace',t)
def lolli(a,b):return f'(.lolli {a} {b})'
def nil(ty):return c(f'(.nil {ty})',f'(.list {ty})')
def cons(ty,d,a,l):
    k=c(f'(.cons {ty})',lolli(D,lolli(ty,lolli(f'(.list {ty})',f'(.list {ty})'))))
    return app(app(app(k,d),a),l)
def typ(t):
    if t[0]=='v':return vars[t[1]]
    if t[0]=='c':return t[2]
    if t[0]=='lam':return lolli(vars[t[1]],typ(t[2]))
    if t[0]=='app':
        if t[3]:return t[3]
        a=typ(t[1]); assert a.startswith('(.lolli '),a
        rem=a[len('(.lolli '):-1]; depth=0
        for i,ch in enumerate(rem):
            if ch=='(':depth+=1
            if ch==')':depth-=1
            if ch==' ' and depth==0:return rem[i+1:]
        raise ValueError(a)
def fv(t):
    if t[0]=='v':return {t[1]}
    if t[0]=='c':return set()
    if t[0]=='lam':return fv(t[2])-{t[1]}
    if t[0]=='brace':return fv(t[1])
    return fv(t[1])|fv(t[2])
def V(i):return f'(⟨{i}, {vars[i]}⟩ : Var)'
def T(t):
    if t[0]=='v':return f'(.var {V(t[1])})'
    if t[0]=='c':return f'(.const {t[1]})'
    if t[0]=='lam':return f'(.lam {V(t[1])} {T(t[2])})'
    if t[0]=='brace':return f'(.brace {T(t[1])})'
    return f'(.app {T(t[1])} {T(t[2])})'
def C(ids):return '['+', '.join(V(i) for i in sorted(ids))+']'
checks='by simp [IsDisjointCtxUnion, DisjointCtx, IsCtxUnion, or_assoc, or_left_comm, or_comm]'
def typed(t,ctx=None):
    if ctx is None:ctx=fv(t)
    assert fv(t)<=ctx,(fv(t),ctx)
    k=t[0]
    if k=='c':return f'(HasType.const {C(ctx)} {t[1]})'
    if k=='v':return f'(HasType.var (Γ := {C(ctx-{t[1]})}) (Γ\' := {C(ctx)}) {V(t[1])} ({checks}))'
    if k=='lam':return f'(HasType.lam (Γ := {C(ctx)}) (Γ\' := {C(ctx|{t[1]})}) {V(t[1])} (by simp [IsCtxUnion] <;> tauto) {typed(t[2],ctx|{t[1]})})'
    if k=='app':
        if t[2][0]=='brace':return f'(HasType.listElim {typed(t[1],ctx)} {typed(t[2][1],set())})'
        right=fv(t[2]);left=ctx-right
        return f'(HasType.app (Γ₁ := {C(left)}) (Γ₂ := {C(right)}) (Γ := {C(ctx)}) ({checks}) {typed(t[1],left)} {typed(t[2],right)})'
    raise ValueError(t)
def subst(t,x,s):
    if t[0]=='v':return s if t[1]==x else t
    if t[0]=='c':return t
    if t[0]=='lam':return t if t[1]==x else lam(t[1],subst(t[2],x,s))
    if t[0]=='brace':return brace(subst(t[1],x,s))
    return app(subst(t[1],x,s),subst(t[2],x,s),t[3])
def listParts(t):
    if t[0]=='c' and t[1].startswith('(.nil '):return []
    if t[0]=='app' and t[1][0]=='app' and t[1][1][0]=='app' and t[1][1][1][0]=='c' and t[1][1][1][1].startswith('(.cons '):
        return [(t[1][1][2],t[1][2])]+listParts(t[2])
    raise ValueError('not list')
def step(t):
    if t[0]!='app':return None
    a,b=t[1:3]
    if a[0]=='lam':
        out=subst(a[2],a[1],b)
        return out,f'(by have h := RedStep.conv (ConvStep.beta {V(a[1])} {T(a[2])} {T(b)}); have heq : substTerm {T(a[2])} {V(a[1])} {T(b)} = {T(out)} := (by simp +decide [substTerm, freeVarOccurrences]); rw [heq] at h; exact h)'
    if a[0]=='app' and a[2][0]=='brace':
        l=a[1];h=a[2][1]
        if l[0]=='c' and l[1].startswith('(.nil '):
            ty=l[1][len('(.nil '):-1]
            return b,f'(RedStep.conv (ConvStep.iterNil {ty} {T(h)} {T(b)}))'
        if l[0]=='app' and l[1][0]=='app' and l[1][1][0]=='app' and l[1][1][1][0]=='c' and l[1][1][1][1].startswith('(.cons '):
            ty=l[1][1][1][1][len('(.cons '):-1];d=l[1][1][2];elem=l[1][2];tail=l[2]
            out=app(app(app(h,d),elem),app(app(tail,brace(h),typ(a)),b))
            return out,f'(RedStep.conv (ConvStep.iterCons {ty} {T(d)} {T(elem)} {T(tail)} {T(h)} {T(b)} ⟨{len(listParts(tail))}, by decide⟩))'
    lstep=step(a)
    if lstep:return app(lstep[0],b,t[3]),f'(RedStep.appLeft {T(b)} {lstep[1]})'
    rstep=step(b)
    if rstep:return app(a,rstep[0],t[3]),f'(RedStep.appRight {T(a)} {rstep[1]})'
    return None

def normal(t):
    if t[0] in ('v','c'):
        return '(by rintro ⟨u, h⟩; cases h with | conv h => cases h)'
    if t[0]=='app':
        return f'''(by
  rintro ⟨u, h⟩
  cases h with
  | conv h => cases h
  | appLeft s h => exact ({normal(t[1])} : IsNormal {T(t[1])}) ⟨_, h⟩
  | appRight t h => exact ({normal(t[2])} : IsNormal {T(t[2])}) ⟨_, h⟩)'''
    raise ValueError(t)
inner=lam(4,lam(5,lam(6,cons(LB,v(4),nil(B),v(6)))))
outer=lam(1,lam(2,lam(3,cons(LB,v(1),nil(B),app(app(v(2),brace(inner),lolli(LLB,LLB)),v(3))))))
f=lam(0,app(app(v(0),brace(outer),lolli(LLB,LLB)),nil(LB)))
l=cons(LB,v(10),cons(B,v(11),c('.tt',B),nil(B)),nil(LB))
t=app(f,l);steps=[]
for i in range(100):
    res=step(t)
    if not res:break
    steps.append((t,res[0],res[1]));t=res[0]
w=t
out=['import Definitions.Def_AehligSchwichtenberg2002_Bounds','import Mathlib.Tactic.Tauto','namespace AehligSchwichtenberg2002.Audit',f'def f : Term := {T(f)}',f'def input : Term := {T(l)}',f'def output : Term := {T(w)}',f'theorem f_typed : HasType [] f (.lolli {LLB} {LLB}) := by\n  exact {typed(f)}',f'theorem input_typed : HasType {C(fv(l))} input {LLB} := by\n  exact {typed(l)}',f'theorem input_normal : IsNormal input := by\n  exact {normal(l)}',f'theorem output_normal : IsNormal output := by\n  exact {normal(w)}','theorem input_canonical : IsCanonicalListInput (.list .bool) input 1 := by',f'  refine ⟨{C(fv(l))}, ?_, input_typed, input_normal, ?_⟩','  · simp','  · decide']
for i,(before,after,proof) in enumerate(steps):out.append(f'theorem step_{i} : RedStep {T(before)} {T(after)} := {proof}')
out+=['theorem reaches_output : RedStar (.app f input) output := by','  exact '+''.join(f'(RedStar.step step_{i} ' for i in range(len(steps)))+'(RedStar.refl _)'+')'*len(steps),'theorem output_has_two_entries : listEntryCount output = some 2 := by decide','theorem output_violates_bound : ¬ ∃ m, listEntryCount output = some m ∧ m ≤ 1 := by','  simp [output_has_two_entries]','#print axioms f_typed','#print axioms input_canonical','#print axioms reaches_output','#print axioms output_normal','#print axioms output_violates_bound','end AehligSchwichtenberg2002.Audit']
out[-1:-1] = ['''def SubmittedCor44 : Prop :=
  ∀ (τ : Ty) (f l w : Term) (n : Nat),
    HasType [] f (.lolli (.list τ) (.list τ)) →
    IsCanonicalListInput τ l n →
    RedStar (.app f l) w → IsNormal w →
    ∃ m : Nat, listEntryCount w = some m ∧ m ≤ n''',
'''theorem submitted_corollary_4_4_false : ¬ SubmittedCor44 := by
  intro h
  exact output_violates_bound
    (h (.list .bool) f input output 1 f_typed input_canonical reaches_output output_normal)''',
'#print axioms submitted_corollary_4_4_false']
(P/'counterexample.lean').write_text('\n\n'.join(out)+'\n')
print('steps',len(steps),'output entries',len(listParts(w)))
