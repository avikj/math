I8=list(range(8)); I12=list(range(12)); I=(I8,[0]*8,I12,[0]*12); SF=(I8,[0]*8,I12,[1]*12)
def comp(g,h):
    gp,go,ge,gf=g; hp,ho,he,hf=h
    return ([gp[hp[i]] for i in range(8)],[(ho[i]+go[hp[i]])%3 for i in range(8)],
            [ge[he[i]] for i in range(12)],[(hf[i]+gf[he[i]])%2 for i in range(12)])
def inv(g):
    p,o,e,f=g; p2=[0]*8;o2=[0]*8;e2=[0]*12;f2=[0]*12
    for i in range(8): p2[p[i]]=i; o2[p[i]]=(-o[i])%3
    for i in range(12): e2[e[i]]=i; f2[e[i]]=(-f[i])%2
    return (p2,o2,e2,f2)
def order(g):
    r=g; k=1
    while r!=I: r=comp(r,g); k+=1
    return k
# CORRECTED: U and D inverted from my first derivation; flips on F,B (Kociemba).
M = {
 'U': inv(([1,2,3,0,4,5,6,7],[0]*8,[1,2,3,0,4,5,6,7,8,9,10,11],[0]*12)),
 'D': inv(([0,1,2,3,7,4,5,6],[0]*8,[0,1,2,3,7,4,5,6,8,9,10,11],[0]*12)),
 'R': ([4,1,2,0,7,5,6,3],[2,0,0,1,1,0,0,2],[8,1,2,3,11,5,6,7,4,9,10,0],[0]*12),
 'L': ([0,2,6,3,4,1,5,7],[0,1,2,0,0,2,1,0],[0,1,10,3,4,5,9,7,8,2,6,11],[0]*12),
 'F': ([1,5,2,3,0,4,6,7],[1,2,0,0,2,1,0,0],[0,9,2,3,4,8,6,7,1,5,10,11],[0,1,0,0,0,1,0,0,1,1,0,0]),
 'B': ([0,1,3,7,4,5,2,6],[0,0,1,2,0,0,2,1],[0,1,2,11,4,5,6,10,8,9,3,7],[0,0,0,1,0,0,0,1,0,0,1,1]),
}
def word(s):
    r=I
    for t in s.split():
        g=M[t[0]]
        p = g if len(t)==1 else (comp(g,g) if t[1]=='2' else inv(g))
        r=comp(r,p)
    return r
def sgn(p):
    return sum(1 for i in range(len(p)) for j in range(i+1,len(p)) if p[i]>p[j])%2
print("generator orders:", {m:order(M[m]) for m in M})
print("invariants on each generator:",
      all(sum(M[m][1])%3==0 and sum(M[m][3])%2==0 and sgn(M[m][0])==sgn(M[m][2]) for m in M))
print("opposite faces commute:", all(comp(M[a],M[b])==comp(M[b],M[a]) for a,b in [('U','D'),('R','L'),('F','B')]))
print()
print("KNOWN FACTS")
print("  superflip from the 20-move FTM word :", word("U R2 F B R B2 R U2 L B2 R U' D' R2 F R' L B2 U2 F2")==SF)
print("  |R U| = 105                         :", order(word("R U"))==105, "(got %d)"%order(word("R U")))
print("  |R U R' U'| = 6                     :", order(word("R U R' U'"))==6, "(got %d)"%order(word("R U R' U'")))
print("  |R U2 D' B D'| = 1260 (max in G)    :", order(word("R U2 D' B D'"))==1260, "(got %d)"%order(word("R U2 D' B D'")))
print("  |sune R U R' U R U2 R'| = 6         :", order(word("R U R' U R U2 R'"))==6, "(got %d)"%order(word("R U R' U R U2 R'")))
print("  superflip is an involution          :", order(SF)==2)
