# Verifies the claims in the proof of Proposition (optimality)(ii):
#  - P_A, P_B are q-Weil polynomials for q >= 8 (and not for q <= 7);
#  - their trace polynomials are h_A, h_B as stated, with the sharp endpoint identity;
#  - they share c_1, c_2, c_3 identically in q but differ at c_4.
R.<q> = PolynomialRing(QQ)
St.<T> = PolynomialRing(R)

PA = T^8 - (q+1)*T^5 - (q^2+q+2)*T^4 - q*(q+1)*T^3 + q^4
PB = T^8 - 2*T^6 - (q+1)*T^5 + (q^2-q)*T^4 - q*(q+1)*T^3 - 2*q^2*T^2 + q^4

# (1) trace polynomials:  P(T) = T^4 * h(T + q/T)
L.<t> = LaurentPolynomialRing(R)
to_L = lambda P: sum(P[k]*t^k for k in range(P.degree()+1))
u = t + q*t^(-1)
hA = u^4 - 4*q*u^2 - (q+1)*u + (q^2-q-2)
hB = u^4 - (4*q+2)*u^2 - (q+1)*u + 3*q*(q+1)
assert t^4*hA == to_L(PA) and t^4*hB == to_L(PB)
print("(1) trace polynomials h_A, h_B verified")

# (2) sharp endpoint identity, in s = sqrt(q)
Rs.<s> = PolynomialRing(QQ)
hAs = s^8/s^4  # placeholder; build h_A(x) with q=s^2
x = polygen(Rs, 'x')
hA_x = x^4 - 4*s^2*x^2 - (s^2+1)*x + (s^4 - s^2 - 2)
assert hA_x(2*s) == (s^2+1)*((s-1)^2 - 3)
print("(2) h_A(2 sqrt q) = (q+1)((sqrt q - 1)^2 - 3) =", factor(hA_x(2*s)))
print("    >= 0  iff  q >= (1+sqrt3)^2 = 4+2sqrt3 = %.4f, i.e. q >= 8" % (4+2*sqrt(3.0)))

# (3) q-Weil exactly for q >= 8 (check integer q in [2,120])
Rx.<X> = PolynomialRing(QQ)
def specialize(P, qq): return sum(QQ(P[k](qq))*X^k for k in range(P.degree()+1))
def is_weil(P, qq):
    return all(abs(abs(z)-sqrt(float(qq))) < 1e-7*sqrt(float(qq))
               for z in specialize(P, qq).roots(CC, multiplicities=False))
bad = [qq for qq in range(2,121) if not (is_weil(PA,qq) and is_weil(PB,qq))]
weil = [qq for qq in range(2,121) if is_weil(PA,qq) and is_weil(PB,qq)]
print("(3) q in [2,120]: both Weil for q =", (min(weil), "..", max(weil)),
      "| NOT both Weil for q =", bad)

# (4) point counts c_n = Res(P, T^n - 1) = #A(F_{q^n}), as polynomials in q
for n in (1,2,3,4):
    cA = PA.resultant(T^n - 1); cB = PB.resultant(T^n - 1)
    same = (cA == cB)
    print("(4) c_%d: equal = %s%s" % (n, same, "" if same else "   (c_%d(A)-c_%d(B) = %s)"%(n,n,cA-cB)))

# (5) cyclotomic norms F_d = Res(P, Phi_d), exactly as quoted in the proof
print("(5) cyclotomic norms F_d (as in the text):")
for d, Phi in [(1, T-1), (2, T+1), (3, T^2+T+1), (4, T^2+1)]:
    FA = PA.resultant(Phi); FB = PB.resultant(Phi)
    if FA == FB:
        print("    F_%d(A)=F_%d(B) = %s" % (d, d, FA))
    else:
        print("    F_%d(A)-F_%d(B) = %s   (distinguishes)" % (d, d, FA-FB))
