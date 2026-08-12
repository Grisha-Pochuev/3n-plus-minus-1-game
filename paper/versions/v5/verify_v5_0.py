#!/usr/bin/env python3
"""Supporting arithmetic, adversarial regression, and control checks for v5.0.

The script checks exact identities used in the proved part, two permanent negative regressions,
claim/package hygiene, and acyclicity of the declared pure-routing graph.
It is supporting verification, not an end-to-end proof of P1, P2, or the infinite theorem.
"""
from __future__ import annotations
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def A(q: int) -> int:
    return (3*q + 1)//2


def asl(n: int) -> int:
    if n == 0:
        return 0
    bits = bin(n)[2:]
    k = 1
    i = len(bits)-1
    while i > 0 and bits[i-1] != bits[i]:
        k += 1
        i -= 1
    return k


def R(n: int) -> int:
    return n >> asl(n)


def B(q: int) -> int:
    return R(A(q))


def Q(r: int, e: int, a: int) -> int:
    return a*(1 << r)-e


def J(s: int) -> int:
    return 2*A(s)+1


def alpha(s: int) -> int:
    return 1-((s//2) % 2)


def v2(n: int) -> int:
    assert n > 0
    return (n & -n).bit_length()-1


def oddpart(n: int) -> int:
    return n >> v2(n)



def kappa(q: int) -> int:
    assert q > 0
    if q % 2 == 0:
        return oddpart(q)
    return oddpart(q+1)


def check_coefficient_pullback(limit=100000):
    for w in range(1,limit+1,2):
        assert kappa(3*w)==J(R(w))
        assert kappa(3*w-1)==J(R(2*w-1))



def check_source_boundary(limit=200000):
    for s in range(1, limit+1):
        e=alpha(s)
        n=3*J(s)+1-2*e
        assert v2(n)==1
        assert oddpart(n)==J(A(s))
        n2=3*J(s)+1-2*(1-e)
        assert v2(n2)>=2
        assert oddpart(n2)==J(B(s))


def constant_tail_coordinates(q: int):
    assert q>0
    if q%2==0:
        r=v2(q); return oddpart(q),r,0
    r=v2(q+1); return oddpart(q+1),r,1


def source_of_odd_coeff(a: int) -> int:
    while a%3==0:
        a//=3
    # invert J by binary search; J is strictly increasing
    lo,hi=0,max(1,a)
    while lo<=hi:
        m=(lo+hi)//2; jm=J(m)
        if jm==a: return m
        if jm<a: lo=m+1
        else: hi=m-1
    raise AssertionError(('not J image',a))


def rho(q: int) -> int:
    a,_,_=constant_tail_coordinates(q)
    return source_of_odd_coeff(a)


def check_boundary_coefficient(limit=100000):
    for a in range(1,limit+1,2):
        for e in (0,1):
            p=B(Q(1,e,a))
            assert p==B(Q(2,e,a))
            if p>0:
                kp=constant_tail_coordinates(p)[0]
                assert 4*kp <= 3*a+1
                if a>=3: assert kp<a
                assert 6*rho(p) <= p-1


def check_a_side(limit=200000):
    for x in range(1,limit+1):
        e=alpha(x); w=Q(1,e,J(x)); y=A(x)
        assert B(w) in (A(y),B(y))


def check_b_transfer_diamond(limit=200000):
    for x in range(1,limit+1):
        e=1-alpha(x); a=J(x); g=1-e
        n=3*a+1-2*e; j=v2(n); y=B(x)
        assert j>=2 and oddpart(n)==J(y)
        P=Q(1,e,a); U=Q(2,e,a)
        D=Q(j,g,J(y)); C=Q(j-1,g,J(y)); F=A(U)
        assert D==A(P) and C==B(P) and C==B(U)
        md={A(D),B(D)}; mc={A(C),B(C)}
        common=md & mc
        assert len(common)==1
        X=next(iter(common)); other=mc-{X}
        assert len(other)==1
        Y=next(iter(other))
        assert B(F)==Y


def check_long_tail(limit=20001, max_r=18):
    for a in range(1, limit+1, 2):
        for e in (0,1):
            for r in range(3,max_r+1):
                assert A(Q(r,e,a)) == Q(r-1,e,3*a)
                assert B(Q(r,e,a)) == Q(r-2,e,3*a)
            assert B(Q(1,e,a)) == B(Q(2,e,a))


def check_fixed_tail_diamond(limit=20001, max_r=18):
    for c in range(1,limit+1,2):
        for e in (0,1):
            for r in range(2,max_r+1):
                X=Q(r,e,3*c); G=Q(r,e,c); H=Q(r+1,e,c); Y=A(G)
                assert A(H)==X
                assert B(H)==Y
                if r==2:
                    assert B(X)==B(Y)
                elif r==3:
                    assert B(X)==A(Y)
                else:
                    assert B(X)==A(Y)


def check_side_relation(limit=100000):
    exc={1,3,12,14}
    for q in range(1,limit+1):
        if q%16 not in exc:
            t=B(A(q)); s=B(q)
            assert t in (A(s), B(s)), (q,s,t,A(s),B(s))
        if q%16 in exc:
            assert A(q)%16 not in exc


def check_base_entry(limit=200000):
    for x in range(1,limit+1):
        a=J(x)
        for e in (0,1):
            P=Q(1,e,a); U=Q(2,e,a); b=B(P)
            assert b==B(U)
            n=9*a+1-2*e
            v=v2(n); g=1-e
            assert oddpart(n)==J(b)
            if e==1-alpha(x):
                assert v==1
                assert b==3*A(x)+1
                T=Q(1,g,J(b)); C=R(T)
                assert C in (A(b),B(b))
            else:
                assert e==alpha(x)
                assert v>=2
                if v>=4:
                    assert b<x
                if v==3:
                    assert J(b)%3==(1+g)%3


def check_zero_source_valuations(max_n=200):
    for n in range(1,max_n+1):
        jplus=v2(3**n+1)
        jminus=v2(3**n-1)
        assert jplus==(2 if n%2 else 1)
        assert jminus==(1 if n%2 else 2+v2(n))
        for e in (0,1):
            N=3**n+1-2*e
            j=v2(N); b=oddpart(N)
            if j==1:
                y=(3**(n-1)-1)//2
                assert b==J(y)
                if e==0:
                    assert R(3**n)==A(y)
                else:
                    assert R(3**n-1)==B(y)





def check_alternating_lift(limit=200000):
    for z in range(1, limit+1):
        delta=1-(z%2)
        r=R(z)
        target=3*z+1
        found=False
        # the theorem gives an exact finite constant-tail exponent
        for m in range(1, max(3, z.bit_length()+2)):
            if Q(m,delta,J(r))==target:
                found=True
                break
        assert found, (z,r,delta,target)


def check_exceptional_side(limit=200000):
    exc={1,3,12,14}
    for q in range(1, limit+1):
        if q%16 not in exc:
            continue
        ell=B(q); p=B(A(q)); v=A(A(q))
        # p is an exact lift over ell and v the adjacent lift.
        delta=(v-2*p)
        assert delta in (0,1), (q,p,v)
        found=False
        for m in range(1, max(3, p.bit_length()+2)):
            if p==Q(m,delta,J(ell)) and v==Q(m+1,delta,J(ell)):
                found=True; break
        assert found, (q,ell,p,v,delta)

def check_hidden_parent(limit_a=20000):
    for a in range(1,limit_a+1,2):
        if a%3==0:
            continue
        for e in (0,1):
            if a%3 != (1+e)%3:
                continue
            H=Q(3,e,a); G=Q(2,e,a)
            num=2*H+e-1
            assert num%3==0
            K=num//3
            assert A(K)==H
            assert B(K)==G


def check_negative_regressions():
    # Permanent regression 1: smaller canonical coefficient does NOT imply
    # smaller coefficient source in the presence of powers of three.
    s=1
    a=3*J(s)
    e=1
    p=B(Q(1,e,a))
    assert p==22
    kp=constant_tail_coordinates(p)[0]
    sp=source_of_odd_coeff(kp)
    assert kp==11 and kp<a
    assert sp==3 and sp>s

    # Permanent regression 2: a B-return after a multi-A streak need NOT
    # descend below the source retained before the streak.
    xs=[20]
    for _ in range(3):
        xs.append(A(xs[-1]))
    assert xs==[20,30,45,68]
    assert [alpha(x) for x in xs]==[1,0,1,1]
    n=3*J(68)+1
    assert v2(n)==3
    assert oddpart(n)==J(25)
    assert B(68)==25 and 25>20


def check_control_certificate():
    data=json.loads((ROOT/'routing_certificate_v5_0.json').read_text())
    assert data['schema_version']==2
    assert data['package_version']=='5.0'
    assert data['status']=='PARTIAL_CLAIM_SAFE'
    controls=set(data['controls'])
    allowed={'pure-routing','strict-source','strict-token','OPEN-P1','OPEN-P2'}
    edges=data['edges']
    assert edges
    for edge in edges:
        assert edge['from'] in controls and edge['to'] in controls, edge
        assert edge['kind'] in allowed, edge
        assert isinstance(edge.get('guard'),str) and edge['guard'].strip(), edge

    # The two previously hidden reset classes must stay visibly open until
    # their mathematical proofs are supplied.
    emap={(e['from'],e['to']):e['kind'] for e in edges}
    assert emap[('b2_ready','a_obligation')]=='OPEN-P1'
    assert emap[('high_return','marked_tail')]=='OPEN-P2'
    assert emap[('terminal_macro','a_obligation')]=='OPEN-P2'
    # The anchor counterexample forbids labelling this edge as source descent.
    assert emap[('b_select','factor_fork')]=='pure-routing'

    # Only proved-as-pure edges are used in the finite DAG check. Open or
    # strict edges may reset controls and are ranked elsewhere / not yet proved.
    pure=[(e['from'],e['to']) for e in edges if e['kind']=='pure-routing']
    adj={v:[] for v in controls}
    indeg={v:0 for v in controls}
    for u,v in pure:
        adj[u].append(v); indeg[v]+=1
    stack=[v for v,d in indeg.items() if d==0]
    topo=[]
    while stack:
        u=stack.pop(); topo.append(u)
        for v in adj[u]:
            indeg[v]-=1
            if indeg[v]==0: stack.append(v)
    assert len(topo)==len(controls), 'declared pure-routing graph contains a cycle'
    rank={v:0 for v in controls}
    for u in reversed(topo):
        if adj[u]: rank[u]=1+max(rank[v] for v in adj[u])
    for u,v in pure:
        assert rank[u]>rank[v]
    return rank


def check_claim_and_package_hygiene():
    tex=(ROOT/'3n_plus_minus_1_game_v5.0.tex').read_text()
    # Active manuscript must point only to the current checker/certificate.
    forbidden=[
        'verify_v3_0.py','verify_v4_0.py','verify_v4.0.py',
        'routing_certificate_v3_0.json','routing_certificate_v4_0.json',
        'v3.0 supporting checks passed','v4.0 supporting checks passed'
    ]
    for token in forbidden:
        assert token not in tex, ('stale active reference',token)
    required=[
        'verify\\_v5\\_0.py',
        'routing\\_certificate\\_v5\\_0.json',
        'OPEN\\_PROOF\\_OBLIGATIONS\\_v5\\_0.md',
        'does not claim that the prize problem is solved',
        'Obligation P1',
        'Obligation P2'
    ]
    for token in required:
        assert token in tex, ('missing claim-safety marker',token)

    files=[
        '3n_plus_minus_1_game_v5.0.tex',
        '3n_plus_minus_1_game_v5.0.pdf',
        'routing_certificate_v5_0.json',
        'OPEN_PROOF_OBLIGATIONS_v5_0.md',
        'README_v5.0.md',
        'SELF_AUDIT_v5.0.md',
        'REPAIR_REPORT_v5.0.md',
        'SOURCE_REVISION_v5.0.md'
    ]
    for name in files:
        assert (ROOT/name).is_file(), ('missing package file',name)


def main():
    check_source_boundary()
    check_coefficient_pullback()
    check_boundary_coefficient()
    check_a_side()
    check_b_transfer_diamond()
    check_long_tail()
    check_fixed_tail_diamond()
    check_side_relation()
    check_base_entry()
    check_zero_source_valuations()
    check_alternating_lift()
    check_exceptional_side()
    check_hidden_parent()
    check_negative_regressions()
    rank=check_control_certificate()
    check_claim_and_package_hygiene()
    print('v5.0 supporting checks passed (claim-safe partial package)')
    print('maximum declared pure-routing control height:', max(rank.values()))
    print('OPEN mathematical obligations: P1, P2')
    print('This output is not a proof of the no-DRAW theorem.')


if __name__=='__main__':
    main()
