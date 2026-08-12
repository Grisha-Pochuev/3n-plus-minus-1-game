#!/usr/bin/env python3
"""Supporting regression checks for closure synthesis v6.3.

The program checks the exact arithmetic identities used by the human proof,
including the two new selector bridges that close the former P1 reset.  It
also checks the permanent counterexamples that forbid the two old shortcuts,
high-return coordinate identities, marked-tail common-child identities, and
the residual finite-control order.  Finite computation is supporting evidence,
not an end-to-end proof of the infinite theorem.
"""
from __future__ import annotations
import argparse
import random

EXCEPTIONAL={1,3,12,14}

def A(q:int)->int:
    if q<0: raise ValueError(q)
    return (3*q+1)//2

def asl(n:int)->int:
    if n<0: raise ValueError(n)
    if n==0:return 0
    k=1; bit=n&1; n>>=1
    while n:
        nb=n&1
        if nb==bit: break
        k+=1; bit=nb; n>>=1
    return k

def R(n:int)->int:
    return n>>asl(n)

def B(q:int)->int:
    return R(A(q))

def J(s:int)->int:
    return 2*A(s)+1

def Q(r:int,e:int,a:int)->int:
    assert r>=0 and e in (0,1) and a>0 and a%2==1
    return a*(1<<r)-e

def alpha(s:int)->int:
    assert s>0
    return 1-((s//2)%2)

def v2(n:int)->int:
    assert n>0
    return (n&-n).bit_length()-1

def oddpart(n:int)->int:
    return n>>v2(n)

def selector(s:int,e:int)->int:
    return A(s) if e==alpha(s) else B(s)

def kappa(q:int)->int:
    assert q>0
    return oddpart(q if q%2==0 else q+1)

def source_of_odd_coeff(a:int)->int:
    assert a>0 and a%2==1
    while a%3==0:a//=3
    # J is increasing and J(s) in {3s+1,3s+2}; a tiny inverse neighbourhood suffices.
    s0=max(0,(a-2)//3)
    for s in range(max(0,s0-2),s0+4):
        if J(s)==a:return s
    raise AssertionError((a,s0))

def constant_tail_coordinates(q:int):
    assert q>0
    if q%2==0:
        r=v2(q); return oddpart(q),r,0
    r=v2(q+1); return oddpart(q+1),r,1

def rho(q:int)->int:
    a,_,_=constant_tail_coordinates(q)
    return source_of_odd_coeff(a)

def check_old_local(limit:int):
    for s in range(1,limit+1):
        e=alpha(s)
        n=3*J(s)+1-2*e
        assert v2(n)==1 and oddpart(n)==J(A(s))
        n=3*J(s)+1-2*(1-e)
        assert v2(n)>=2 and oddpart(n)==J(B(s))
    for a in range(1,min(limit,30000)+1,2):
        for e in (0,1):
            assert B(Q(1,e,a))==B(Q(2,e,a))
            for r in range(3,14):
                assert A(Q(r,e,a))==Q(r-1,e,3*a)
                assert B(Q(r,e,a))==Q(r-2,e,3*a)
    for x in range(1,limit+1):
        if x%16 not in EXCEPTIONAL:
            assert B(A(x)) in (A(B(x)),B(B(x)))
        else:
            assert A(x)%16 not in EXCEPTIONAL

def check_raw_selector(limit:int):
    for s in range(1,limit+1):
        for e in (0,1):
            got=R(Q(1,e,J(s)))
            want=selector(s,e)
            assert got==want,(s,e,got,want)

def check_second_selector(limit:int):
    counts={'ordinary':0,'B2':0,'exceptional_B':0}
    for q in range(1,limit+1):
        eB=1-alpha(q)
        j=v2(3*J(q)+1-2*eB)
        if q%16 in EXCEPTIONAL:
            counts['exceptional_B']+=1
            assert j>=4,(q,j)
            continue
        y=B(q); g=alpha(q)
        got=B(A(q)); want=selector(y,g)
        assert got==want,(q,y,g,got,want,alpha(y))
        counts['ordinary']+=1
        if j==2:
            counts['B2']+=1
            assert q%16 not in EXCEPTIONAL
            assert selector(y,g)==B(A(q))
    return counts

def check_a_canonical_selector(limit:int):
    # If an A-selecting obligation continues canonically to y=A(x), its
    # previous common side is exactly the source selected by the next phase.
    for x in range(1,limit+1):
        e=alpha(x); g=1-e; y=A(x)
        common=B(Q(1,e,J(x)))
        assert common==selector(y,g),(x,e,y,g,common,selector(y,g))

def check_b_transfer(limit:int):
    for x in range(1,limit+1):
        e=1-alpha(x); g=1-e
        n=3*J(x)+1-2*e; j=v2(n); y=B(x)
        assert j>=2 and oddpart(n)==J(y)
        P=Q(1,e,J(x)); U=Q(2,e,J(x))
        D=Q(j,g,J(y)); C=Q(j-1,g,J(y)); F=A(U)
        assert D==A(P) and C==B(P) and C==B(U)
        common=set((A(D),B(D))) & set((A(C),B(C)))
        assert len(common)==1
        X=next(iter(common)); other=set((A(C),B(C)))-{X}
        assert len(other)==1
        assert B(F)==next(iter(other))

def check_base_entry(limit:int):
    for x in range(1,limit+1):
        a=J(x)
        for e in (0,1):
            b=B(Q(1,e,a)); assert b==B(Q(2,e,a))
            n=9*a+1-2*e; vv=v2(n); g=1-e
            assert oddpart(n)==J(b)
            if e==1-alpha(x):
                assert vv==1 and b==3*A(x)+1
                assert R(Q(1,g,J(b))) in (A(b),B(b))
            else:
                assert vv>=2
                if vv>=4: assert b<x
                if vv==3: assert J(b)%3==(1+g)%3

def check_high_return_coordinates(limit_t:int,max_v:int):
    # Exact high-return coordinates and phase table used by the repaired P2.
    for t in range(1,limit_t+1):
        for g in (0,1):
            for vv in range(7,max_v+1):
                u=Q(vv-1,g,J(t))
                c=Q(vv-3,g,3*J(t))
                p=B(A(u))
                assert p==A(c)==Q(vv-4,g,9*J(t)),(t,g,vv)
                assert c%16 not in EXCEPTIONAL
                assert p%16 not in EXCEPTIONAL
                b=B(p)
                assert b==Q(vv-6,g,27*J(t)),(t,g,vv,b,Q(vv-6,g,27*J(t)))
                n=3*J(b)+1-2*g
                j=v2(n)
                sel=source_of_odd_coeff(oddpart(n))
                if vv==7:
                    assert j==1 and sel==A(b),(t,g,vv,j,sel,A(b))
                elif vv==8:
                    assert j>=3 and sel==B(b),(t,g,vv,j,sel,B(b))
                else:
                    assert j==2 and sel==B(b),(t,g,vv,j,sel,B(b))

def check_attached_lift(limit_a:int,max_m:int):
    for a in range(1,limit_a+1,2):
        for g in (0,1):
            e=1-g
            for m in range(2,max_m+1):
                x=Q(m,g,a)
                assert alpha(x)==e
                y=A(x)
                common=B(Q(1,e,J(x)))
                if m==2:
                    assert common==9*a-g
                elif m==3:
                    assert common==R(Q(1,g,9*a))
                else:
                    assert common==Q(m-3,g,9*a)
                n=3*J(y)+1-2*g
                j=v2(n)
                if m==2: assert j==1
                elif m==3: assert j>=3
                else:
                    assert j==2
                    assert oddpart(n)==J(common)

def check_marked_tail_and_short_rows(limit_t:int,max_D:int):
    # Exact marked-tail identities used by the P2 closure.
    for t in range(1,limit_t+1):
        for g in (0,1):
            C=27*J(t)
            for D in range(3,max_D+1):
                b=Q(D,g,C); q=A(b); y=B(b)
                if D==3:
                    assert B(q)==B(y),(t,g,D)
                else:
                    r=B(q)
                    assert r==A(y)==Q(D-3,g,9*C),(t,g,D,r,A(y))
            # D=1: the coarse j=1 branch is impossible; every return is an
            # actual child of the retained LOSS y=A(b).
            b=Q(1,g,C); q=B(b); y=A(b)
            n=9*J(b)+1-2*g; j=v2(n); w=source_of_odd_coeff(oddpart(n))
            assert j>=2,(t,g,j)
            if j==2:
                assert w==A(y),(t,g,j,w,A(y))
            else:
                assert w==B(y),(t,g,j,w,B(y))
            # D=2: valuation one, exact lift over retained LOSS y=B(b).
            b=Q(2,g,C); q=A(b); y=B(b)
            n1=9*J(b)+1-2*g; j=v2(n1); w=source_of_odd_coeff(oddpart(n1))
            assert j==1,(t,g,j)
            assert rho(w)==y,(t,g,w,y,rho(w))
            # The next factor numerator is exactly one ordinary source-boundary
            # transition of the lift w in the opposite phase.
            n2=27*J(b)+1-2*g
            assert n2==3*n1-2*(1-2*g)
            assert n2==2*(3*J(w)+1-2*(1-g)),(t,g,w,n2)


def check_D3_raw_and_two_bit_terminal(limit_C:int):
    # Exact shortest-marked-row raw lift and its zero-recycle m=2 arithmetic.
    for C in range(1,limit_C+1,2):
        for g in (0,1):
            b=Q(3,g,C); q=A(b); y=B(b); r=B(q)
            assert r==B(y)
            # First signed/raw factor exit from the D=3 marked frame.
            n1=9*J(b)+1-2*g
            assert v2(n1)==1
            w=source_of_odd_coeff(oddpart(n1))
            T=Q(1,1-g,J(w)); S=R(T)
            m=1+v2(27*C+1-2*g)
            assert m>=2
            assert S==Q(m,g,J(r)),(C,g,m,S,Q(m,g,J(r)))
            # At m=2 the common side of O(S,1-g) is A(A(S)), exactly the
            # two-bit terminal row used in the human proof.
            if m==2:
                x=S; e=1-g
                d=B(Q(1,e,J(x)))
                assert d==A(A(x)),(C,g,x,d,A(A(x)))
                c=B(x); p=B(A(x))
                if x%16 in EXCEPTIONAL:
                    # Arithmetic exceptional pair is an exact adjacent lift
                    # over c (outcomes are handled by the human proof).
                    d0=A(A(x)); p0=B(A(x))
                    assert rho(d0)==c and rho(p0)==c,(C,g,x,c,d0,p0,rho(d0),rho(p0))


def check_D2_exact_loss_anchor(limit_C:int):
    # D=2 exact returned lift: for positive retained LOSS source y, the tail
    # exponent is one plus the actual alternating-suffix length of z=3C-g.
    # Also verify the universal first factor-source trichotomy used by the
    # LOSS-anchored module.
    for C in range(1,limit_C+1,2):
        for g in (0,1):
            b=Q(2,g,C); y=B(b)
            n=9*J(b)+1-2*g
            assert v2(n)==1
            w=source_of_odd_coeff(oddpart(n))
            if y>0:
                z=3*C-g
                m=asl(z)+1
                d=1-g
                assert m>=2
                assert w==Q(m,d,J(y)),(C,g,y,w,m,Q(m,d,J(y)))
            else:
                assert rho(w)==0,(C,g,w,rho(w))
    for y in range(1,limit_C+1):
        for f in (0,1):
            n=9*J(y)+1-2*f
            v=v2(n); t=source_of_odd_coeff(oddpart(n))
            if v==1:
                assert rho(t)==B(y),(y,f,v,t,rho(t),B(y))
            elif v==2:
                assert t==A(A(y)),(y,f,v,t,A(A(y)))
            else:
                assert t==B(A(y)),(y,f,v,t,B(A(y)))

def check_attached_b(limit_r:int):
    for r in range(1,limit_r+1):
        for d in (0,1):
            S=Q(1,d,J(r)); e=1-d
            assert e==1-alpha(S)
            k=B(S)
            if k>0:
                assert rho(k)<r,(r,d,S,k,rho(k))

def check_negative_regressions():
    s=1; a=3*J(s); e=1
    p=B(Q(1,e,a))
    assert p==22 and kappa(p)==11 and source_of_odd_coeff(kappa(p))==3
    assert kappa(p)<a and 3>s
    xs=[20]
    for _ in range(3): xs.append(A(xs[-1]))
    assert xs==[20,30,45,68]
    assert B(68)==25 and 25>20
    # The repaired proof compares the immediate local predecessor, not 20.
    assert B(68)<68

def check_large_random(samples:int,bits:int,seed:int=20260810):
    rng=random.Random(seed)
    for _ in range(samples):
        s=rng.getrandbits(bits) or 1
        for e in (0,1):
            assert R(Q(1,e,J(s)))==selector(s,e)
        if s%16 not in EXCEPTIONAL:
            y=B(s); g=alpha(s)
            assert B(A(s))==selector(y,g)
        else:
            e=1-alpha(s)
            assert v2(3*J(s)+1-2*e)>=4


def check_short_rows_random(samples:int,bits:int,seed:int=20260811):
    rng=random.Random(seed)
    for _ in range(samples):
        C=(rng.getrandbits(bits)|1)
        for g in (0,1):
            b=Q(1,g,C); y=A(b)
            n=9*J(b)+1-2*g; j=v2(n); w=source_of_odd_coeff(oddpart(n))
            assert j>=2
            assert w==(A(y) if j==2 else B(y))
            b=Q(2,g,C); y=B(b)
            n1=9*J(b)+1-2*g; assert v2(n1)==1
            w=source_of_odd_coeff(oddpart(n1)); assert rho(w)==y
            n2=27*J(b)+1-2*g
            assert n2==2*(3*J(w)+1-2*(1-g))

def check_control_order():
    c={
      'marked':9,'boundary':8,'short':8,'obligation':7,
      'A4':6,'A3':5,'A2':4,'A1':3,'b-select':2,'loss-entry':2,
      'b2-first':1,'factor':1,'b2-ready':0,'high-return':0,'terminal':0,
    }
    pure=[
      ('marked','short'),('boundary','obligation'),('boundary','factor'),
      ('short','obligation'),('obligation','A4'),('obligation','factor'),
      ('A4','A3'),('A4','b-select'),('A3','A2'),('A3','b-select'),
      ('A2','A1'),('A2','b-select'),('A1','b-select'),
      ('b-select','b2-first'),('loss-entry','factor'),
      ('b2-first','b2-ready'),('factor','high-return')]
    for u,v in pure: assert c[u]>c[v],(u,v,c[u],c[v])
    # The dangerous reset edges are deliberately absent from the pure graph.
    forbidden={('b2-ready','obligation'),('high-return','marked'),
               ('high-return','terminal'),('terminal','obligation')}
    assert not forbidden.intersection(pure)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--limit',type=int,default=250000)
    ap.add_argument('--random-samples',type=int,default=5000)
    ap.add_argument('--random-bits',type=int,default=256)
    args=ap.parse_args()
    L=args.limit
    check_old_local(L)
    check_raw_selector(L)
    check_a_canonical_selector(L)
    counts=check_second_selector(L)
    check_b_transfer(min(L,200000))
    check_base_entry(min(L,200000))
    check_high_return_coordinates(limit_t=min(5000,max(100,L//50)),max_v=22)
    check_attached_lift(limit_a=10001,max_m=18)
    check_D3_raw_and_two_bit_terminal(limit_C=min(20001,max(501,L//10)))
    check_marked_tail_and_short_rows(limit_t=min(3000,max(100,L//100)),max_D=18)
    check_D2_exact_loss_anchor(min(200000,max(1000,L)))
    check_attached_b(min(L,200000))
    check_negative_regressions()
    check_large_random(args.random_samples,args.random_bits)
    check_short_rows_random(args.random_samples,args.random_bits)
    check_control_order()
    print('V6.3 SUPPORTING REGRESSIONS PASSED')
    print(f'finite sources checked: 1..{L}')
    print('second-selector counts:',counts)
    print(f'random selector samples: {args.random_samples} at {args.random_bits} bits')
    print('scope: arithmetic/control regressions only; human proof carries outcomes/ranks')

if __name__=='__main__':
    main()
