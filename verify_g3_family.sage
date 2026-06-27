# Verifies the claims in the proof of Proposition (optimality)(i), g=3 family.
# The point is that being q-Weil is PROVED FOR ALL q via the trace polynomial:
#   P(T) = prod_i (T^2 - beta_i T + q),  h(T) = prod_i (T - beta_i),
# and P is q-Weil  <=>  all beta_i in [-2 sqrt q, 2 sqrt q]; moreover
#   #A(F_q) = P(1) = prod_i ((1+q) - beta_i) = h(1+q).
# We check: (1) P = trace-poly of h; (2) sign alternation -,+,-,+ of h at
# -2rq,-rq,rq,2rq (=> three roots in [-2rq,2rq] for q>=2); (3) #A(F_q)=h(1+q)
# agree and c_2 differs; (4) ordinariness.
R.<q> = PolynomialRing(QQ)
St.<T> = PolynomialRing(R)

PA = T^6 - T^3 + q^3
PB = T^6 + T^4 - (q+2)*T^3 + q*T^2 + q^3
hA = T^3 - 3*q*T - 1
hB = T^3 - (3*q-1)*T - (q+2)

# (1) trace polynomials: P(T) = T^g * h(T + q/T)
L.<t> = LaurentPolynomialRing(R)
to_L = lambda P: sum(P[k]*t^k for k in range(P.degree()+1))
u = t + q*t^(-1)
hA_u = u^3 - 3*q*u - 1                # h_A(t + q/t)
hB_u = u^3 - (3*q-1)*u - (q+2)        # h_B(t + q/t)
assert t^3*hA_u == to_L(PA) and t^3*hB_u == to_L(PB)
print("(1) trace polynomials: P_A=tracepoly(h_A), P_B=tracepoly(h_B) verified")

# (2) root location: values of h at -2rq,-rq,rq,2rq alternate -,+,-,+ (in s=sqrt q)
Rs.<s> = PolynomialRing(QQ); x = polygen(Rs,'x')
for name,h in [("h_A", x^3 - 3*s^2*x - 1), ("h_B", x^3 - (3*s^2-1)*x - (s^2+2))]:
    vals = [factor(h(c)) for c in (-2*s,-s,s,2*s)]
    print("(2) %s at (-2,-1,1,2)*sqrt q:" % name)
    for pt,v in zip(("-2rq","-rq"," rq"," 2rq"), vals):
        print("      %s : %s" % (pt, v))

# (3) point counts via cyclotomic resultants; #A(F_q)=c_1=h(1+q)
cA = {n: PA.resultant(T^n-1) for n in (1,2)}; cB = {n: PB.resultant(T^n-1) for n in (1,2)}
assert cA[1] == hA(1+q) == hB(1+q) == cB[1]
print("(3) #A(F_q)=c_1(A)=c_1(B)=h(1+q)=%s ;  c_2(A)-c_2(B)=%s (distinguishes)"
      % (cA[1], factor(cA[2]-cB[2])))

# (4) ordinariness: middle coeff (coeff of T^g=T^3) a unit mod p
print("(4) a_3:  A=%s (ordinary all q),  B=%s (ordinary iff p odd);  P_A != P_B: %s"
      % (PA[3], PB[3], PA != PB))
