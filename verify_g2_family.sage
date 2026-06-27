# Verifies the claims in the proof of Proposition (optimality)(i), g=2 family.
# Being q-Weil is PROVED FOR ALL q via the trace polynomial:
#   P(T) = prod_i (T^2 - beta_i T + q),  h(T) = prod_i (T - beta_i),
# and P is q-Weil  <=>  all beta_i in [-2 sqrt q, 2 sqrt q]; moreover
#   #A(F_q) = P(1) = h(1+q).  Here both trace polys have explicit roots in range.
R.<q> = PolynomialRing(QQ)
St.<T> = PolynomialRing(R)

PA = T^4 + (q-2)*T^2 + q^2
PB = T^4 - T^3 + (2*q-1)*T^2 - q*T + q^2
hA = T^2 - (q+2)             # roots +- sqrt(q+2), and q+2 <= 4q for q>=1
hB = T^2 - T - 1             # roots (1 +- sqrt5)/2, modulus < 2 <= 2 sqrt q

# (1) trace polynomials: P(T) = T^g * h(T + q/T)
L.<t> = LaurentPolynomialRing(R)
to_L = lambda P: sum(P[k]*t^k for k in range(P.degree()+1))
u = t + q*t^(-1)
hA_u = u^2 - (q+2)           # h_A(t + q/t)
hB_u = u^2 - u - 1           # h_B(t + q/t)
assert t^2*hA_u == to_L(PA) and t^2*hB_u == to_L(PB)
print("(1) trace polynomials: P_A=tracepoly(h_A), P_B=tracepoly(h_B) verified")

# (2) roots of h in [-2 sqrt q, 2 sqrt q]:
#     h_A roots^2 = q+2 <= 4q  (q>=1);  h_B roots = (1+-sqrt5)/2, |.| < 2 <= 2 sqrt q.
print("(2) h_A roots +-sqrt(q+2), in range since q+2<=4q (q>=1);"
      " h_B roots (1+-sqrt5)/2 of modulus <2<=2sqrt q (q>=1)")

# (3) point counts; #A(F_q)=c_1=h(1+q)
cA = {n: PA.resultant(T^n-1) for n in (1,2)}; cB = {n: PB.resultant(T^n-1) for n in (1,2)}
assert cA[1] == hA(1+q) == hB(1+q) == cB[1]
print("(3) #A(F_q)=c_1(A)=c_1(B)=h(1+q)=%s ;  c_2(A)-c_2(B)=%s (distinguishes)"
      % (cA[1], factor(cA[2]-cB[2])))

# (4) ordinariness: middle coeff (coeff of T^g=T^2) a unit mod p
print("(4) a_2:  A=%s (ordinary iff p odd),  B=%s (ordinary all q);  P_A != P_B: %s"
      % (PA[2], PB[2], PA != PB))
