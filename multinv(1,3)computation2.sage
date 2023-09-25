d = 1
e = 3

'''
R = Q[V3 ox V1][x,y,z] with variables a_ij (i and j indicates weight in V3 and V1 respectively)

Rb = Q[V4 o+ V2][x] with variables b_ij (i indicates the representation V(4-i), j indicates the weight)

btoa: the list of square matrices, block decomposition of V3 ox V1 <- V4 o+ V2 by weights)
atob: the list of square matrices, block decomposition of V3 ox V1 -> V4 o+ V2 by weights)
'''

avars = ['a' + str(floor(i/(d+1))) + str(i % (d+1)) for i in range((d+1)*(e+1))]
avars.append('x')
avars.append('y')
avars.append('z')
R = PolynomialRing(QQ, avars)
F = FractionField(R)
def btoa(d,e):
    a = list()
    for i in range(d+e+1):
        mat = list()
        r = min(i,d,e,d+e-i)
        for j in range(r+1):
            row = list()
            l = min(d,e) - min(d,e,d+e-i)
            for k in range(r+1):
#                print(i,l,j,k,r)
                if(j == i):
                    if(k == 0): row.append(1)
                    else: row.append((-1) * row[k-1] * (max(d,e)-i+k)/(min(d,e)-k+1))
                else:
                    s = 0
                    if(l == 0):
                        if(k != r or i > r): s += (i-k) * a[i-1][j][k]
                        if(k != 0): s += k * a[i-1][j][k-1]
                    else:
                        s += (k+l) * a[i-1][j][k] + (i-k-l) * a[i-1][j][k+1]
                    s /= i-j
                    row.append(s)
#            print(row)
            mat.append(row)
        a.append(mat)
    return a

def atob(d,e):
    a = btoa(d,e)
    re = list()
    for i in range(d+e+1):
        re.append(matrix(a[i])^-1)
    return re

def homatob(Rb,d,e):
    mats = atob(d,e)
    homlist = list()
    for i in range(d+e+1):
        slist = list()
        for j in range(min(i,d+e-i,d,e)+1):
            slist.append(Rb.gen((d+e-j+1)*j + i))
        slist = list(mats[i] * vector(slist))
        homlist.append(slist)
    retlist = list()
    for i in range((d+1)*(e+1)):
        j = floor(i / (d+1))
        k = i % (d+1)
        l = j+k
        m = k-max(l-max(d,e),0)
        retlist.append(homlist[l][m])
    return retlist

'''
f(z): the rational map given by f(x,y)
canform(x,y): the canonical bicoavriant f(x,y) of V_3 ox V_1

omega(f,x,y,a,b): Omega_{x,y} f(x,y) of order(a,b) bicovariant f(x,y)
cgprod(f,g,x,r): the transvectant (f,g)_r w.r.t. the covariant variable x
'''

def f(z):
    den = 0;
    num = 0;
    for i in range(d+e):
        den -= z ** i * R.gen(i)
        k = Integer(d+e+i)
        num += z ** i * R.gen(k)
    return num/den

def canform(x,y):
    num = (d+1) * (e+1)
    return sum([ R.gen(i) * x^(floor(i / (d+1))) * y^(i % (d+1)) for i in range(num)])

def omega(f,x,y,a,b):
    fx = f.derivative(x)
    fy = f.derivative(y)
    return (fy * a - x * fy.derivative(x)) - (fx * b - y * fx.derivative(y))

def binom(n,k):
    return binomial(n,k)

def cgprod(f,g,x,r):
    fdeg = f.degree(x)
    gdeg = g.degree(x)
    flist = [f.coefficient({x:i}) for i in range(fdeg+1)]
    glist = [g.coefficient({x:i}) for i in range(gdeg+1)]
    return sum([ (binom(i,k) * binom(fdeg-i,r-k) * binom(j,r-k) * binom(gdeg-j,k) * binom(r,k)^-1 * binom(fdeg,r)^-1 * binom(gdeg,r)^-1) * (-1)^k * flist[i] * glist[j] * x^(i+j-r) for k in range(r+1) for i in range(fdeg+1) for j in range(max(0,r-i),gdeg+1)])

'''
multdegvecs(val,degs):
input: val: list(nonnegative integers) v
       degs: list(list(nonnegative integers)) D = [d1,d2,...dn], di = [di1,..., dim]
output: list(list(positive integers))  [a = [a1,...,an] \in NN^n | sum(ai*di) = v]

remark: works only for the last minor of the matrix D is nondegenerate.
'''

def multdegvecs(val,degs):
    deglist = [[]]
    lendeg = len(degs)
    degdim = len(degs[0])
    for i in range(lendeg-degdim):
        nowdeglist = deglist.copy()
        deglist = []
        for x in nowdeglist:
            xdeg = [sum([x[j] * degs[j][k] for j in range(i)]) for k in range(degdim)]
            ithmax = 100
            for k in range(degdim):
                if degs[i][k] > 0:
                    ithmax = min(ithmax, (val[k]-xdeg[k])/degs[i][k])
            for j in range(-floor(-ithmax)+1):
                deglist.append(x + [j])
    inv = matrix([degs[i] for i in range(lendeg-degdim,lendeg)]).inverse()
    nowdeglist = deglist.copy()
    deglist = []
    for x in nowdeglist:
        degrem = [val[k] - sum([x[j] * degs[j][k] for j in range(lendeg - degdim)]) for k in range(degdim)]
        invdeg = list(inv * vector(degrem))
        if(invdeg == [floor(invdeg[k]) for k in range(degdim)] == [abs(invdeg[k]) for k in range(degdim)]):
            deglist.append(x + invdeg)
    return deglist

num = (d+1)*(e+1)
x = R.gen(num)
y = R.gen(num+1)
z = R.gen(num+2)

'''
Rb : algebra with SL2-action QQ[V + V_1] for V = V_4 + V_2.
expressions :
  basis of V_4 : b00 -- b04
  basis of V_2 : b10 -- b12
  basis of V_1 : (x,1)
covariants are named as
  f104,f012 : generating covariant of V_4,V_2
  iab : invariant, deg a in V_4, deg b in V_2
  cabc : covariant, deg a in V_4, deg b in V_2, deg c in V_1

Remark : the invariants i20,i02,i30,i12,i22,i33 are respectively named i,d,j,a,b,c in West's paper.
'''

bvars = sum([['b' + str(i) + str(j) for j in range(d+e+1 - 2*i)] for i in range(min(d,e)+1)],[])
bvars.append('x')
Rb = PolynomialRing(QQ, bvars)
#Fb = FractionField(R)

xb = Rb.gen(num)

hatob = homatob(Rb,d,e) + [Rb.gen((d+1)*(e+1)) for i in range(3)]
hatob = R.hom(hatob, Rb)

f012 = Rb.gen(5) + Rb.gen(6) * xb + Rb.gen(7) * xb^2
f104 = Rb.gen(0) + Rb.gen(1) * xb + Rb.gen(2) * xb^2 + Rb.gen(3) * xb^3 + Rb.gen(4) * xb^4

i02 = cgprod(f012,f012,xb,2)
i20 = cgprod(f104,f104,xb,4)
c112 = cgprod(f012,f104,xb,2)
c114 = cgprod(f012,f104,xb,1)
c204 = cgprod(f104,f104,xb,2)

i30 = cgprod(f104,c204,xb,4)
i12 = cgprod(f104,f012^2,xb,4)
c122 = cgprod(f104,f012^2,xb,3)
c212 = cgprod(c204,f012,xb,2)
c214 = cgprod(c204,f012,xb,1)
c306 = cgprod(c204,f104,xb,1)

i22 = cgprod(c204,f012^2,xb,4)
c222 = cgprod(c204,f012^2,xb,3)
c314 = cgprod(c306,f012,xb,2)

c322 = cgprod(c306,f012^2,xb,4)

i33 = cgprod(c306,f012^3,xb,6)

'''
per2: a covariant which indicates 2nd periodic points
df2: a covariant which is given by (\Omega^1\Psi_2f)(z,z)

You can check by computing the following:

af2 = canform(x,z).polynomial(z).resultant(canform(z,y).polynomial(z))
aper2 = canform(x,z).polynomial(z).resultant(canform(z,x).polynomial(z))
adf2 = omega(R(af2),x,y,9,1)

per2 = Rb(hatob(af2)/f104)
per2-(c306-1/4*f104*c112-1/4*f012*c204+1/8*f012*c114 - f012^3/32)
df2 = hatob(adf2)
df2 - (9/2*c204^2 - 9/2*i20*f104^2 - 1/8*i02*f104^2 + 6*c306*f012 + c112*f104*f012 - 13/8*c204*f012^2 - 1/2*f012^2*c114 + 5/128 * f012^4)
'''

per2 = (c306-1/4*f104*c112-1/4*f012*c204+1/8*f012*c114 - f012^3/32)
df2 = (9/2*c204^2 - 9/2*i20*f104^2 - 1/8*i02*f104^2 + 6*c306*f012 + c112*f104*f012 - 13/8*c204*f012^2 - 1/2*f012^2*c114 + 5/128 * f012^4)


'''
dr,drm: the resultants res(f104, f104.derivative(xb) +,- xb*f102)
discf22: the remaining factor of discriminant of per2, computed in discper2 (see more of this file)
'''

dr  = 32*(i20^3 - 6 * i30^2) + 48*i20*i22 - 48 * i30*i12 - 32 * i33 + i12^2 - 4*i22*i02 + 2/3*i20*i02^2
drm = 32*(i20^3 - 6 * i30^2) + 48*i20*i22 - 48 * i30*i12 + 32 * i33 + i12^2 - 4*i22*i02 + 2/3*i20*i02^2


discf22 = (i02^3 - 12*i02^2*i20 + 48*i02*i20^2 - 64*i20^3 + 384*i30^2 + 288*i30*i12 + 54*i12^2)




def rand(n):
    return ZZ.random_element(n)

def resx(f,g,x):
    return f.polynomial(x).resultant(g.polynomial(x))

'''
T = QQ[b0,b1,b2,x,t] : algebra to use as values of interpolation

V = QQ[x02,x20,x30,x12,x22,x33] : the algebra represents the invariant algebra I(V4 o+ V2)
(to use .factor(), we do not introduce the relation)
'''


T = PolynomialRing(QQ, ['b0','b1','b2','x','t'],order = 'lex')

b0 = T.gen(0)
b1 = T.gen(1)
b2 = T.gen(2)
xx = T.gen(3)
t = T.gen(4)
vallist = [b0,b0,b0,b0,b0,b1,b1,b1]

V = PolynomialRing(QQ,['x02','x20','x30','x12','x22','x33','t'])
x02,x20,x30,x12,x22,x33,Vt = tuple(V.gens())

dr0 = 32*(x20^3 - 6 * x30^2)
dr2 = 48*x20*x22 - 48 * x30*x12
dr3 = - 32 * x33
dr4 = x12^2 - 4*x22*x02 + 2/3*x20*x02^2

drx = 32*(x20^3 - 6 * x30^2) + 48*x20*x22 - 48 * x30*x12 - 32 * x33 + x12^2 - 4*x22*x02 + 2/3*x20*x02^2
drmx= 32*(x20^3 - 6 * x30^2) + 48*x20*x22 - 48 * x30*x12 + 32 * x33 + x12^2 - 4*x22*x02 + 2/3*x20*x02^2
i33r= x33^2-(-1/108*x02^3*x20^3 + 1/18*x02^3*x30^2 + 1/24*x02*x20^2*x12^2 + 1/6*x30*x12^3 - 1/2*x02*x30*x12*x22 - 1/4*x20*x12^2*x22 + 1/4*x02*x20*x22^2 + 1/2*x22^3)


homVR = V.hom([i02,i20,i30,i12,i22,i33,0],Rb)

'''
testi332,resp2p1,discper2,multorb2 : test functions
    for a randomly chosen element [n1,...,n8] of V4 o+ V2,
    a function which returns a value of covariant with degrees.

    F:
    testi332 : i33^2
    resp2p1 : res( Per_2^* , Per_1=f4 )
    discper2 : disc( Per_2^*)
    multorb2 : res( Per_2^* , f4 * d(Per_2^*) + df2 * t)

    output: tuple([n1,...,n8] , F(n1*b0,..., n5*b0,n6*b1,...,n8*b1) in T).
'''

def testi332():
    randlist = [rand(100) for i in range(8)]
    randvar = [randlist[i] * vallist[i] for i in range(8)] + [xx]
    homrand = Rb.hom(randvar,T)
    res = homrand(i33^2)
    return randlist,res

'''
i332data = datamake(15,testi332)
interpolate_invariant(i332data)
result: -1/108*x02^3*x20^3 + 1/18*x02^3*x30^2 + 1/24*x02*x20^2*x12^2 + 1/6*x30*x12^3 - 1/2*x02*x30*x12*x22 - 1/4*x20*x12^2*x22 + 1/4*x02*x20*x22^2 + 1/2*x22^3
'''

def resp2p1():
    randlist = [rand(100) for i in range(8)]
    randvar = [randlist[i] * vallist[i] for i in range(8)] + [xx]
    homrand = Rb.hom(randvar,T)
    hper2 = homrand(per2)
    if(hper2.coefficient({xx : 6}) == 0):
        print("head coeff vanishing")
        return [0 for i in range(7)],T(0)
    hf0 = homrand(f104)
    res = T(resx(hper2,hf0,xx))
    return randlist,res
'''
respdata = datamake(40,resp2p1)
rp2p1 = interpolate_invariant(respdata)
factor(rp2p1)

result: 2^-20 * drm^2 * dr
'''

def discper2():
    randlist = [rand(100) for i in range(8)]
    randvar = [randlist[i] * vallist[i] for i in range(8)] + [xx]
    homrand = Rb.hom(randvar,T)
    hper2 = homrand(per2)
    if(hper2.coefficient({xx : 6}) == 0):
        print("head coeff vanishing")
        return [0 for i in range(7)],T(0)
    res = T(discriminant(hper2.polynomial(xx)))
    return randlist,res
'''
dp2data = datamake(75,discper2)
dp2 = interpolate_invariant(dp2data)
result: 2^-34 * drm^2 * dr * discf22^2
'''

def mulorb2():
    randlist = [rand(100) for i in range(8)]
    randvar = [randlist[i] * vallist[i] for i in range(8)] + [xx]
    homrand = Rb.hom(randvar,T)
    hper2 = homrand(per2)
    if(hper2.coefficient({xx : 6}) == 0):
        print("head coeff vanishing")
        return [0 for i in range(7)],T(0)
    hder2s = t * homrand(df2) + hper2.derivative(xx) * homrand(f104)
    res = T(hder2s.polynomial(xx).resultant(hper2.polynomial(xx)) / hper2.coefficient({xx : 6}))
    res = T(sqrt(res/(homrand(drm)^4)))
    res = res * sgn( res.coefficient({t:0})/(homrand(dr)*homrand(discf22)) )
    return randlist,res

'''
mo2data = datamake(40,mulorb2)
mo2 = interpolate_invariant(mo2data)

result: coefftcients of t^0,t^1,t^2,t^3:
[(1/402653184) * (-2*x02^2*x20 - 96*x20^3 + 576*x30^2 + 144*x30*x12 - 3*x12^2 + 12*x02*x22 - 144*x20*x22 + 96*x33) * (x02^3 - 12*x02^2*x20 + 48*x02*x20^2 - 64*x20^3 + 384*x30^2 + 288*x30*x12 + 54*x12^2),
(-1/805306368) * (-22*x02^2*x20 + 864*x20^3 - 5184*x30^2 + 144*x30*x12 - 33*x12^2 + 132*x02*x22 - 144*x20*x22 + 576*x33) * (x02^3 - 12*x02^2*x20 + 48*x02*x20^2 - 64*x20^3 + 384*x30^2 + 288*x30*x12 + 54*x12^2),
(-1/6442450944) * (306*x02^5*x20 - 2072*x02^4*x20^2 - 20544*x02^3*x20^3 + 300800*x02^2*x20^4 - 1691136*x02*x20^5 + 3483648*x20^6 + 96192*x02^3*x30^2 - 1286400*x02^2*x20*x30^2 + 10146816*x02*x20^2*x30^2 - 16920576*x20^3*x30^2 + 1008*x02^3*x30*x12 + 42432*x02^2*x20*x30*x12 + 1430784*x02*x20^2*x30*x12 - 4451328*x20^3*x30*x12 + 459*x02^3*x12^2 + 14316*x02^2*x20*x12^2 - 6768*x02*x20^2*x12^2 - 775104*x20^3*x12^2 - 1836*x02^4*x22 + 6624*x02^3*x20*x22 + 173568*x02^2*x20^2*x22 - 1850880*x02*x20^3*x22 + 4672512*x20^4*x22 - 23887872*x30^4 - 10616832*x30^3*x12 - 156672*x30^2*x12^2 + 244224*x30*x12^3 + 26136*x12^4 - 589824*x02*x30^2*x22 + 9289728*x20*x30^2*x22 - 672768*x02*x30*x12*x22 + 4202496*x20*x30*x12*x22 - 111744*x02*x12^2*x22 + 39168*x20*x12^2*x22 + 28800*x02^2*x22^2 - 460800*x02*x20*x22^2 + 1382400*x20^2*x22^2 - 2208*x02^3*x33 + 103296*x02^2*x20*x33 - 1027584*x02*x20^2*x33 + 2598912*x20^3*x33 + 9289728*x30^2*x33 + 3280896*x30*x12*x33 - 76032*x12^2*x33 - 230400*x02*x22*x33 + 921600*x20*x22*x33),
(1/57982058496) * (1458*x02^5*x20 + 2904*x02^4*x20^2 - 43072*x02^3*x20^3 + 2453760*x02^2*x20^4 - 11570688*x02*x20^5 + 40310784*x20^6 - 358464*x02^3*x30^2 - 10056960*x02^2*x20*x30^2 + 69424128*x02*x20^2*x30^2 - 259780608*x20^3*x30^2 - 1296*x02^3*x30*x12 - 730944*x02^2*x20*x30*x12 + 12379392*x02*x20^2*x30*x12 - 58973184*x20^3*x30*x12 + 2187*x02^3*x12^2 + 100188*x02^2*x20*x12^2 - 730224*x02*x20^2*x12^2 - 1881792*x20^3*x12^2 - 8748*x02^4*x22 - 95328*x02^3*x20*x22 + 2674944*x02^2*x20^2*x22 - 20113920*x02*x20^3*x22 + 82861056*x20^4*x22 + 107495424*x30^4 + 17915904*x30^3*x12 - 3856896*x30^2*x12^2 - 2521728*x30*x12^3 + 143748*x12^4 + 18413568*x02*x30^2*x22 - 161243136*x20*x30^2*x22 + 8280576*x02*x30*x12*x22 - 21399552*x20*x30*x12*x22 - 693792*x02*x12^2*x22 + 5664384*x20*x12^2*x22 + 475200*x02^2*x22^2 - 12787200*x02*x20*x22^2 + 43545600*x20^2*x22^2 + 7776*x02^3*x33 + 1173888*x02^2*x20*x33 - 7921152*x02*x20^2*x33 + 49268736*x20^3*x33 - 6912000*x22^3 - 71663616*x30^2*x33 - 3981312*x30*x12*x33 + 1672704*x12^2*x33 - 5529600*x02*x22*x33 + 49766400*x20*x22*x33)]
'''


def degnummax(example):
    g = 0
    deglist = [[0,2],[2,0],[3,0],[1,2],[2,2]]
    for m in example.monomials():
        mb0 = m.degree(b0)
        mb1 = m.degree(b1)
        if(mb1 % 2 == 1):
            mb0 = mb0-3
            mb1 = mb1-3
        g = max(g,len(multdegvecs([mb0,mb1],deglist)))
    return g


def degbs(m):
    return [m.degree(b0),m.degree(b1)]

'''
datamake:
input: numofdata : positive integer n
       testfcn : some test function
output: list of n returns of testfcn.
        print out the progress (as each 10 data are constructed)
        and time of computation after the construction finished.
'''

def datamake(numofdata,testfcn):
    ti = cputime()
    data = []
    for i in range(numofdata):
        data.append(testfcn())
        if(i % 10 == 9):
            print(str(i+1) + " data are constructed.")
    print("data make : finished in " + str(cputime(ti)) + " sec")
    return data

'''
interpolate_invariant():
input: list of outputs of test function: [[[n1,...,n8], F(n1*b0 ,..., n8*b1)] : n chosen randomly]
output: the invariant in V which represents F
        prints each degree of outputs.
'''


def interpolate_invariant(data):
    ti = cputime()
    example = data[0]
    mons = example[1].monomials()
    monsps = []
    monspart = []
    oldm = mons[0]
    for m in mons:
        if degbs(oldm) == degbs(m):
            monspart.append(m)
        else:
            oldm = m
            monsps.append(monspart.copy())
            monspart = [m]
    monsps.append(monspart)
    print("monomial partition : finished in " + str(cputime(ti)) + " sec")
    print("part length = " + str(len(monsps)))
    deglist = [[0,2],[2,0],[3,0],[1,2],[2,2]]
    invlist = [i02,i20,i30,i12,i22,i33,1]
    count = 1
    respoly = 0

    for part in monsps:
        print("part" + str(count))
        print(part)
        count = count+1
        mat = [[QQ(p[1].coefficient(m).constant_coefficient()) for p in data] for m in part]
        print("value matrix constructed, total time : " + str(cputime(ti)) + " sec.")
        mat2 = []
        degs = degbs(part[0])
        remdegs = [int(degs[1] % 2 == 1),0]
        if(degs[1] % 2 == 1):
            degs[0] = degs[0] - 3
            degs[1] = degs[1] - 3
        constdegs = multdegvecs(degs,deglist)
        valmonoms = [V.monomial(*(l + remdegs)) for l in constdegs]
        print("number of fundamental invariants is : " + str(len(constdegs)))
        for p in data:
            homp = Rb.hom( list(p[0])+[1] , T)
            invvals = [homp(i) for i in invlist]
            homV = V.hom(invvals,QQ)
            mat2.append([homV(q) for q in valmonoms])
        mat2 = list(matrix(mat2).transpose())
        print("fundamental matrix constructed, total time : " + str(cputime(ti)) + " sec.")
        mat = matrix(mat + mat2)
        kermod = mat.kernel()
        kerbase = kermod.basis()
        if(len(kerbase) != len(part)):
            print("unexpected kernel dimension! kernel : " + str(len(kerbase)) + " expected : " + str(len(part)))
            kerbase = kerbase[0:len(part)]
        exvalmonoms = [0 for m in part] + valmonoms
        remmonoms = [V.gen(6)^(m.degree(t)) for m in part]
        valpolyn = vector(remmonoms) * matrix(kerbase) * vector(exvalmonoms)
        respoly = respoly + valpolyn
        print("partial computation finished in total " + str(cputime(ti)) + " sec. the result is")
        print(valpolyn)
    return respoly

'''
For example, the computation of mo2 proceeds like this.

mo2data = datamake(40,mulorb2)
mo2 = interpolate_invariant(mo2data)

prints like this:

10 data are constructed.
20 data are constructed.
30 data are constructed.
40 data are constructed.
data make : finished in 23.457604000000003 sec
monomial partition : finished in 0.00017500000001291482 sec
part length = 10
part1
[b0^12*t^3, b0^12*t^2, b0^12*t, b0^12]
value matrix constructed, total time : 0.000818000000037955 sec.
number of fundamental invariants is : 3
fundamental matrix constructed, total time : 0.04263200000002598 sec.
partial computation finished in total 0.051083000000062384 sec. the result is
729/1048576*x20^6*t^3 - 567/1048576*x20^6*t^2 - 2349/524288*x20^3*x30^2*t^3 + 9/131072*x20^6*t + 1377/524288*x20^3*x30^2*t^2 + 243/131072*x30^4*t^3 + 1/65536*x20^6 - 27/32768*x20^3*x30^2*t + 243/65536*x30^4*t^2 - 3/16384*x20^3*x30^2 + 81/32768*x30^4*t + 9/16384*x30^4
part2
[b0^10*b1^2*t^3, b0^10*b1^2*t^2, b0^10*b1^2*t, b0^10*b1^2]
value matrix constructed, total time : 0.052537000000029366 sec.
number of fundamental invariants is : 6
fundamental matrix constructed, total time : 0.09129300000006424 sec.
partial computation finished in total 0.10081800000006069 sec. the result is
-837/4194304*x02*x20^5*t^3 + 1101/4194304*x02*x20^5*t^2 + 2511/2097152*x02*x20^2*x30^2*t^3 - 2133/2097152*x20^3*x30*x12*t^3 + 2997/2097152*x20^4*x22*t^3 - 27/524288*x02*x20^5*t - 3303/2097152*x02*x20^2*x30^2*t^2 + 1449/2097152*x20^3*x30*x12*t^2 - 1521/2097152*x20^4*x22*t^2 + 81/262144*x30^3*x12*t^3 - 729/262144*x20*x30^2*x22*t^3 - 3/262144*x02*x20^5 + 81/262144*x02*x20^2*x30^2*t - 39/131072*x20^3*x30*x12*t - 3/262144*x20^4*x22*t + 27/16384*x30^3*x12*t^2 - 189/131072*x20*x30^2*x22*t^2 + 9/131072*x02*x20^2*x30^2 - 3/32768*x20^3*x30*x12 + 3/131072*x20^4*x22 + 117/65536*x30^3*x12*t + 9/131072*x20*x30^2*x22*t + 9/16384*x30^3*x12 - 9/65536*x20*x30^2*x22
part3
[b0^9*b1^3*t^3, b0^9*b1^3*t^2, b0^9*b1^3*t, b0^9*b1^3]
value matrix constructed, total time : 0.10154600000004166 sec.
number of fundamental invariants is : 2
fundamental matrix constructed, total time : 0.1464690000000246 sec.
partial computation finished in total 0.1528210000000172 sec. the result is
891/1048576*x20^3*x33*t^3 - 423/1048576*x20^3*x33*t^2 - 81/65536*x30^2*x33*t^3 + 3/65536*x20^3*x33*t - 189/131072*x30^2*x33*t^2 - 1/65536*x20^3*x33 - 9/32768*x30^2*x33*t + 3/32768*x30^2*x33
part4
[b0^8*b1^4*t^3, b0^8*b1^4*t^2, b0^8*b1^4*t, b0^8*b1^4]
value matrix constructed, total time : 0.1534639999999854 sec.
number of fundamental invariants is : 9
fundamental matrix constructed, total time : 0.19220999999998867 sec.
partial computation finished in total 0.2070550000000253 sec. the result is
355/8388608*x02^2*x20^4*t^3 - 1175/25165824*x02^2*x20^4*t^2 - 1455/8388608*x02^2*x20*x30^2*t^3 + 1791/8388608*x02*x20^2*x30*x12*t^3 - 1089/33554432*x20^3*x12^2*t^3 - 1455/4194304*x02*x20^3*x22*t^3 + 35/3145728*x02^2*x20^4*t + 1675/8388608*x02^2*x20*x30^2*t^2 - 1863/8388608*x02*x20^2*x30*x12*t^2 + 4037/33554432*x20^3*x12^2*t^2 + 1205/4194304*x02*x20^3*x22*t^2 - 279/4194304*x30^2*x12^2*t^3 + 333/1048576*x02*x30^2*x22*t^3 - 387/1048576*x20*x30*x12*x22*t^3 + 1575/2097152*x20^2*x22^2*t^3 + 5/1572864*x02^2*x20^4 - 35/524288*x02^2*x20*x30^2*t - 9/1048576*x02*x20^2*x30*x12*t - 127/2097152*x20^3*x12^2*t + 5/262144*x02*x20^3*x22*t + 51/2097152*x30^2*x12^2*t^2 + 3/32768*x02*x30^2*x22*t^2 - 171/262144*x20*x30*x12*x22*t^2 - 225/1048576*x20^2*x22^2*t^2 - 5/262144*x02^2*x20*x30^2 + 9/524288*x02*x20^2*x30*x12 - 13/1048576*x20^3*x12^2 - 5/262144*x02*x20^3*x22 + 327/1048576*x30^2*x12^2*t - 33/524288*x02*x30^2*x22*t + 27/524288*x20*x30*x12*x22*t + 93/524288*x30^2*x12^2 + 3/262144*x02*x30^2*x22 - 27/262144*x20*x30*x12*x22
part5
[b0^7*b1^5*t^3, b0^7*b1^5*t^2, b0^7*b1^5*t, b0^7*b1^5]
value matrix constructed, total time : 0.20821599999999307 sec.
number of fundamental invariants is : 3
fundamental matrix constructed, total time : 0.24378500000000258 sec.
partial computation finished in total 0.24938400000002048 sec. the result is
-573/4194304*x02*x20^2*x33*t^3 + 669/4194304*x02*x20^2*x33*t^2 - 9/131072*x30*x12*x33*t^3 + 225/262144*x20*x22*x33*t^3 - 9/262144*x02*x20^2*x33*t - 267/524288*x30*x12*x33*t^2 - 75/524288*x20*x22*x33*t^2 + 3/262144*x02*x20^2*x33 - 27/131072*x30*x12*x33*t + 9/131072*x30*x12*x33
part6
[b0^6*b1^6*t^3, b0^6*b1^6*t^2, b0^6*b1^6*t, b0^6*b1^6]
value matrix constructed, total time : 0.25026200000002063 sec.
number of fundamental invariants is : 10
fundamental matrix constructed, total time : 0.2994719999999802 sec.
partial computation finished in total 0.3206329999999866 sec. the result is
-673/905969664*x02^3*x20^3*t^3 + 107/33554432*x02^3*x20^3*t^2 - 1867/301989888*x02^3*x30^2*t^3 - 423/33554432*x02^2*x20*x30*x12*t^3 - 5071/402653184*x02*x20^2*x12^2*t^3 + 387/8388608*x02^2*x20^2*x22*t^3 + 1/4194304*x02^3*x20^3*t - 501/33554432*x02^3*x30^2*t^2 - 221/33554432*x02^2*x20*x30*x12*t^2 + 141/134217728*x02*x20^2*x12^2*t^2 - 113/4194304*x02^2*x20^2*x22*t^2 - 2189/50331648*x30*x12^3*t^3 + 599/4194304*x02*x30*x12*x22*t^3 + 1639/16777216*x20*x12^2*x22*t^3 - 925/4194304*x02*x20*x22^2*t^3 - 1/2097152*x02^3*x20^3 + 27/4194304*x02^3*x30^2*t + 21/2097152*x02^2*x20*x30*x12*t + 33/16777216*x02*x20^2*x12^2*t - 21/2097152*x02^2*x20^2*x22*t - 159/4194304*x30*x12^3*t^2 + 219/2097152*x02*x30*x12*x22*t^2 - 51/8388608*x20*x12^2*x22*t^2 + 75/1048576*x02*x20*x22^2*t^2 - 125/1048576*x22^3*t^3 + 3/2097152*x02^3*x30^2 - 3/524288*x02^2*x20*x30*x12 - 3/8388608*x02*x20^2*x12^2 + 3/524288*x02^2*x20^2*x22 + 9/4194304*x30*x12^3*t - 99/2097152*x02*x30*x12*x22*t + 81/8388608*x20*x12^2*x22*t + 9/524288*x30*x12^3 + 9/1048576*x02*x30*x12*x22 - 81/4194304*x20*x12^2*x22
part7
[b0^5*b1^7*t^3, b0^5*b1^7*t^2, b0^5*b1^7*t, b0^5*b1^7]
value matrix constructed, total time : 0.3213969999999904 sec.
number of fundamental invariants is : 3
fundamental matrix constructed, total time : 0.35877299999998513 sec.
partial computation finished in total 0.36355700000001434 sec. the result is
1019/50331648*x02^2*x20*x33*t^3 - 269/16777216*x02^2*x20*x33*t^2 + 121/4194304*x12^2*x33*t^3 - 25/262144*x02*x22*x33*t^3 + 9/1048576*x02^2*x20*x33*t + 99/8388608*x12^2*x33*t^2 + 75/2097152*x02*x22*x33*t^2 - 3/1048576*x02^2*x20*x33 - 81/2097152*x12^2*x33*t + 27/2097152*x12^2*x33
part8
[b0^4*b1^8*t^3, b0^4*b1^8*t^2, b0^4*b1^8*t, b0^4*b1^8]
value matrix constructed, total time : 0.3642929999999751 sec.
number of fundamental invariants is : 7
fundamental matrix constructed, total time : 0.4000419999999849 sec.
partial computation finished in total 0.4104159999999979 sec. the result is
121/2415919104*x02^4*x20^2*t^3 + 259/805306368*x02^4*x20^2*t^2 - 3/134217728*x02^3*x30*x12*t^3 + 2783/1610612736*x02^2*x20*x12^2*t^3 - 331/201326592*x02^3*x20*x22*t^3 - 11/33554432*x02^4*x20^2*t - 21/134217728*x02^3*x30*x12*t^2 - 1193/536870912*x02^2*x20*x12^2*t^2 - 69/67108864*x02^3*x20*x22*t^2 + 1331/536870912*x12^4*t^3 - 803/67108864*x02*x12^2*x22*t^3 + 275/33554432*x02^2*x22^2*t^3 + 1/16777216*x02^4*x20^2 - 3/16777216*x02^3*x30*x12*t + 33/33554432*x02^2*x20*x12^2*t + 9/4194304*x02^3*x20*x22*t - 1089/268435456*x12^4*t^2 + 291/16777216*x02*x12^2*x22*t^2 - 75/16777216*x02^2*x22^2*t^2 + 3/8388608*x02^3*x30*x12 - 3/16777216*x02^2*x20*x12^2 - 3/4194304*x02^3*x20*x22 + 297/134217728*x12^4*t - 297/33554432*x02*x12^2*x22*t - 27/67108864*x12^4 + 27/16777216*x02*x12^2*x22
part9
[b0^3*b1^9*t^3, b0^3*b1^9*t^2, b0^3*b1^9*t, b0^3*b1^9]
value matrix constructed, total time : 0.411611999999991 sec.
number of fundamental invariants is : 1
fundamental matrix constructed, total time : 0.44581499999998186 sec.
partial computation finished in total 0.4504309999999805 sec. the result is
9/67108864*x02^3*x33*t^3 + 23/67108864*x02^3*x33*t^2 - 3/4194304*x02^3*x33*t + 1/4194304*x02^3*x33
part10
[b0^2*b1^10*t^3, b0^2*b1^10*t^2, b0^2*b1^10*t, b0^2*b1^10]
value matrix constructed, total time : 0.45153699999997343 sec.
number of fundamental invariants is : 3
fundamental matrix constructed, total time : 0.5026839999999879 sec.
partial computation finished in total 0.507569999999987 sec. the result is
27/1073741824*x02^5*x20*t^3 - 51/1073741824*x02^5*x20*t^2 + 81/2147483648*x02^3*x12^2*t^3 - 81/536870912*x02^4*x22*t^3 + 11/402653184*x02^5*x20*t - 153/2147483648*x02^3*x12^2*t^2 + 153/536870912*x02^4*x22*t^2 - 1/201326592*x02^5*x20 + 11/268435456*x02^3*x12^2*t - 11/67108864*x02^4*x22*t - 1/134217728*x02^3*x12^2 + 1/33554432*x02^4*x22

'''

