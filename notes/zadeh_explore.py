"""Finite exploratory parity executions; certificates are not Lean proofs."""
from itertools import product


def counter(n):
    centres = [(i, j) for i in range(n) for j in range(2) if i+j<n]
    nodes = [('b',i) for i in range(n)] + [('g',i) for i in range(n)]
    nodes += [(s,i,j,k) for s in ('d','e') for i,j in centres for k in range(2)]
    nodes += [(s,i,j) for s in ('s','F','h') for i,j in centres] + [('t',)]
    t=('t',)
    b=lambda i: ('b',i) if i<n else t
    g=lambda i: ('g',i) if i<n else t
    out={}; pri={}; sig={}; opp=[]
    for v in nodes:
        s=v[0]
        i=v[1] if len(v)>1 else 0
        if s=='b': out[v]=[g(i),b(i+1)]; pri[v]=3;sig[v]=b(i+1)
        if s=='g': out[v]=[('F',i,j) for j in range(2) if i+j<n];pri[v]=11+2*i;sig[v]=('F',i,0)
        if s=='d':
            _,i,j,k=v;out[v]=[('F',i,j),('e',i,j,k)];pri[v]=3;sig[v]=('e',i,j,k)
        if s=='e': out[v]=[b(1),g(0)];pri[v]=3;sig[v]=b(1)
        if s=='s':
            _,i,j=v;out[v]=[('h',i,j),b(0)];pri[v]=10-2*j;sig[v]=out[v][j]
        if s=='F':
            _,i,j=v;out[v]=[('d',i,j,0),('d',i,j,1),('s',i,j)];pri[v]=6-2*j;opp.append(v)
        if s=='h':
            _,i,j=v;out[v]=[b(i+2) if j==0 else g(i+1)];pri[v]=12+2*i
        if s=='t': out[v]=[t];pri[v]=1
    return nodes,out,pri,sig,opp,b,g


def execution(n,limit=2000,fast=False,mdp=False):
    nodes,out,pri,sig,opp,b,g=counter(n)
    E=[(v,w) for v in nodes if v in sig for w in out[v]]
    labels={e:k for k,e in enumerate(E)}
    count=dict.fromkeys(E,0)

    def cmp(a,c):
        p,A,l=a;q,B,m=c
        r=lambda k:k if k%2==0 else -k
        if r(p)!=r(q): return -1 if r(p)<r(q) else 1
        counts=lambda S,p:sum(pri[v]==p for v in S)
        diff=[p for p in {pri[v] for v in A|B} if counts(A,p)!=counts(B,p)]
        if diff:
            top=max(diff)
            good=(counts(A,top)<counts(B,top))==(top%2==0)
            return -1 if good else 1
        if l==m:return 0
        return (-1 if l<m else 1) if p%2 else (-1 if m<l else 1)

    def vals():
        result={}
        for choices in product(range(3),repeat=len(opp)):
            nxt={v:(sig[v] if v in sig else out[v][choices[opp.index(v)]] if v in opp else out[v][0]) for v in nodes}
            for v in nodes:
                seen={};path=[];u=v
                while u not in seen:seen[u]=len(path);path.append(u);u=nxt[u]
                cyc=path[seen[u]:];p=max(pri[w] for w in cyc)
                k=next(k for k,w in enumerate(path) if pri[w]==p)
                a=(p,frozenset(w for w in path[:k] if pri[w]>p),k)
                if v not in result or cmp(a,result[v])<0:result[v]=a
        return result

    def sinkvals():
        M=len(nodes)+1
        dist={('t',):0}
        weights={v:(-M)**pri[v]*M+1 for v in nodes}
        for _ in range(len(nodes)+1):
            new=dict(dist)
            for v in nodes:
                if v==('t',):continue
                ws=[sig[v]] if v in sig else out[v]
                candidates=[dist[w] for w in ws if w in dist]
                if candidates:new[v]=weights[v]+min(candidates)
            if new==dist:
                assert len(new)==len(nodes)
                return new
            dist=new
        raise RuntimeError('negative cycle or no sink path')

    if fast:
        vals=sinkvals
        cmp=lambda a,b:(a>b)-(a<b)

    if mdp:
        from fractions import Fraction as Q
        N=7*n;epsilon=Q(1,N**(2*n+11)+1)
        index={v:i for i,v in enumerate(nodes)}
        def mdpvals():
            size=len(nodes)
            matrix=[[Q(int(i==j)) for j in range(size)]+[Q(0)] for i in range(size)]
            for v in nodes:
                i=index[v]
                if v==('t',):continue
                if v[0] in ('g','s','h'):matrix[i][-1]=Q((-N)**pri[v])
                if v[0]=='F':
                    for k,w in enumerate(out[v]):matrix[i][index[w]]-=epsilon if k==2 else (1-epsilon)/2
                else:matrix[i][index[sig[v] if v in sig else out[v][0]]]-=1
            for k in range(size):
                p=next((i for i in range(k,size) if matrix[i][k]),None)
                if p is None:raise RuntimeError('singular Bellman matrix')
                matrix[k],matrix[p]=matrix[p],matrix[k]
                lead=matrix[k][k]
                if lead!=1:matrix[k]=[x/lead for x in matrix[k]]
                for i in range(size):
                    if i!=k and matrix[i][k]:
                        a=matrix[i][k]
                        matrix[i]=[x-a*y for x,y in zip(matrix[i],matrix[k])]
            return {v:matrix[index[v]][-1] for v in nodes}
        vals=mdpvals
        cmp=lambda a,b:(a>b)-(a<b)

    def closed(i,j): return sig.get(('d',i,j,0))==('F',i,j) and sig.get(('d',i,j,1))==('F',i,j)
    def half(i,j,t):
        return any(sig.get(('d',i,j,k))==('F',i,j) and sig.get(('d',i,j,1-k))!=('F',i,j) and sig.get(('e',i,j,1-k))==t for k in range(2))
    def bits():
        beta=[0]*(n+1)
        for i in reversed(range(n)):beta[i]=int(closed(i,beta[i+1]))
        return beta
    def canonical(number):
        bit=lambda i:(number>>i)&1
        centres=[(i,j) for i in range(n) for j in range(2) if i+j<n]
        if any(sig[('e',i,j,k)]!=(g(0) if bit(0) else b(1)) for i,j in centres for k in range(2)):return False
        for i in range(n):
            j=bit(i+1)
            if bit(i):
                if sig[b(i)]!=g(i) or not closed(i,j) or closed(i,1-j) or sig[g(i)]!=('F',i,j):return False
            else:
                if sig[b(i)]!=b(i+1) or closed(i,j):return False
                if closed(i,1-j) and sig[g(i)]!=('F',i,1-j):return False
                if not closed(i,0) and not closed(i,1) and sig[g(i)]!=('F',i,j if mdp else 0):return False
        if any(sig[('s',i,j)]!=(('h',i,j) if j==bit(i+1) else b(0)) for i,j in centres):return False
        if number<(1<<n)-1:
            nextbit=((number+1)&-(number+1)).bit_length()-1
            if any(sig[('d',i,j,k)]==('F',i,j) for i,j in centres if i==nextbit for k in range(2)):return False
        return True
    def group(e):
        v,w=e;s=v[0]
        if s=='g':return 0
        if s=='d':return 6 if w==('F',v[1],v[2]) else 1
        if s=='e':return 2 if sig[('d',*v[1:])]==('F',v[1],v[2]) else 5
        if s=='b':return 3
        if s=='s':return 4
        return 7
    def before(e,f,target,beta):
        ge=group(e);gf=group(f)
        if ge!=gf:return ge<gf
        u,v=e[0],f[0];i=u[1];k=v[1]
        if ge==4:return i>k
        if ge==5:return i>k or (i==k and ((u[2]!=beta[i+1])<(v[2]!=beta[k+1]) if mdp else u[2]<v[2]))
        if ge==2:
            if i!=k:return i>k
            j=u[2];l=v[2]
            if closed(i,j)!=closed(k,l):return closed(i,j)
            if not closed(i,j) and half(i,j,target)!=half(k,l,target):return half(i,j,target)
            return (j!=beta[i+1])<(l!=beta[k+1]) if mdp else j<l
        if ge==6:
            j,x=u[2:];l,y=v[2:]
            oe=sig[('d',i,j,1-x)]==('F',i,j)
            of=sig[('d',k,l,1-y)]==('F',k,l)
            return (oe,beta[i],i,j!=beta[i+1],x)<(of,beta[k],k,l!=beta[k+1],y)
        return False

    trace=[];source_number=0
    assert canonical(0)
    for step in range(limit):
        if source_number<(1<<n)-1 and canonical(source_number+1):source_number+=1
        V=vals();I=[e for e in E if cmp(V[sig[e[0]]],V[e[1]])<0]
        if not I:return step,trace
        low=min(count[e] for e in I);J=[e for e in I if count[e]==low]
        target=g(0) if cmp(V[b(1)],V[g(0)])<0 else b(1)
        beta=bits()
        rank=lambda e:sum(before(f,e,target,beta) for f in E)*len(E)+labels[e]
        special=(('s',0,1),('h',0,1));entry=(b(0),b(1))
        e=special if special in I and entry in I and count[special]==count[entry]==0 else min(J,key=rank)
        if e not in J:raise RuntimeError(('not-least-entered',e,low))
        if source_number<(1<<n)-1:
            source_target=g(0) if (source_number+1)%2 else b(1)
            source_rank=lambda e:sum(before(f,e,source_target,beta) for f in E)*len(E)+labels[e]
            source_choice=special if special in I and entry in I and count[special]==count[entry]==0 else min(J,key=source_rank)
            if e!=source_choice:raise RuntimeError(('source-rule-disagreement',step,source_number,e,source_choice))
        trace.append((step,e,count[e],sum(x<<i for i,x in enumerate(beta[:-1]))))
        sig[e[0]]=e[1];count[e]+=1
    raise RuntimeError(('limit',limit))


if __name__=='__main__':
    import sys
    fast='--fast' in sys.argv
    mdp='--mdp' in sys.argv
    for n in map(int,[a for a in sys.argv[1:] if a not in ('--fast','--mdp')] or [1,2,3]):
        steps,trace=execution(n,fast=fast,mdp=mdp)
        print({'context':'mdp' if mdp else 'parity','n':n,'iterations':steps,'lower_bound':2**n},flush=True)
