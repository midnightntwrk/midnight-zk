# This script is used to generate the params required in src/ecc/hash_to_curve/

# SageMath version: 10.0
# run the script: sage scripts/hash_to_jubjub_params.sage

# See the constants defined in: https://github.com/zkcrypto/jubjub?tab=readme-ov-file
# the base field of JubJub
p = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
Fp = GF(p) 

# Edwards curve: e(x, y) = a * x^2 + y^2 - 1 - d * x^2 * y^2
ED_a = Fp(-1)
ED_d = Fp(-1) * Fp(10240) / Fp(10241)

# Montgomery curve: m(x, y) = x^3 + J * x^2 - K * y^2 + x
# Transform relation between Montgomery and Edwards, see: https://www.rfc-editor.org/rfc/rfc9380.html#appx-rational-map
MONT_J = Fp(2) * (ED_a + ED_d) / (ED_a - ED_d)
MONT_K = Fp(4) /(ED_a - ED_d)

# Weierstrass curve: w(x, y) = x^3 - y^2 + A * x + B
# Transform relation between Montgomery and Weierstrass, see: https://www.rfc-editor.org/rfc/rfc9380.html#appx-rational-map
WEI_A = (Fp(3) - MONT_J ** 2) / (Fp(3) * MONT_K ** 2)
WEI_B = (Fp(2) * MONT_J ** 3 - Fp(9) * MONT_J) / (Fp(27) * MONT_K ** 3)

# Define the polynomial ring in variables x, y
P.<x, y> = PolynomialRing(Fp, 2)
K = FractionField(P)
x, y = K.gens()

# Edwards curve equation
edwards_form = ED_a * x ** 2 + y ** 2 - 1 - ED_d * x ** 2 * y ** 2

# Montgomery form equation
montgomery_form = x * x * x + MONT_J * x ** 2 - MONT_K * y * y  + x

# Weierstrass curve equation
weierstrass_form = x ** 3 - y * y + WEI_A * x + WEI_B

# Given (x, y) in Weierstrass curve, convert to the point in Montgomery curve
# Algorithm from: https://www.rfc-editor.org/rfc/rfc9380.html#appendix-D.2-5
def weierstrass_to_montgomery(x, y):
    return ((Fp(3) * MONT_K * x - MONT_J) / Fp(3), y * MONT_K)

# Algorithm from: https://www.rfc-editor.org/rfc/rfc9380.html#appendix-D.1-12
def montgomery_to_edwards(s, t):
    tv1 = s + 1
    tv2 = tv1 * t        # (s + 1) * t
    # tv2 = inv0(tv2)      # 1 / ((s + 1) * t)
    if tv2 != 0:
        tv2 = 1 / tv2
    v = tv2 * tv1      # 1 / t
    v = v * s          # s / t
    w = tv2 * t        # 1 / (s + 1)
    tv1 = s - 1
    w = w * tv1        # (s - 1) / (s + 1)
    # e = tv2 == 0
    # w = CMOV(w, 1, e)  # handle exceptional case
    if tv2 == 0:
        w = 1
    return (v, w)

# Test n random points for the correctness of equation transforms
def test(n):
    for i in range(n):
        E = EllipticCurve(Fp, [WEI_A, WEI_B])
        P = E.random_point()
        (a, b) = P.xy()
        not_on_weierstrass = weierstrass_form(a, b) != 0

        (c, d) = weierstrass_to_montgomery(a, b)
        not_on_montgomery = montgomery_form(c, d) != 0

        (e, f) = montgomery_to_edwards(c, d) 
        not_on_edwards = edwards_form(e, f) != 0
    
        if not_on_montgomery | not_on_weierstrass | not_on_edwards:
            print("The random point is not on the curve!")
            return
    
    print("The test for equation transforms is passed")

# Find constant z for svdw method
def find_z_svdw(F, A, B, init_ctr=1):
    g = lambda x: F(x)^3 + F(A) * F(x) + F(B)
    h = lambda Z: -(F(3) * Z^2 + F(4) * A) / (F(4) * g(Z))
    # NOTE: if init_ctr=1 fails to find Z, try setting it to F.gen()
    ctr = init_ctr
    while True:
        for Z_cand in (F(ctr), F(-ctr)):
            # Criterion 1:
            #   g(Z) != 0 in F.
            if g(Z_cand) == F(0):
                continue
            # Criterion 2:
            #   -(3 * Z^2 + 4 * A) / (4 * g(Z)) != 0 in F.
            if h(Z_cand) == F(0):
                continue
            # Criterion 3:
            #   -(3 * Z^2 + 4 * A) / (4 * g(Z)) is square in F.
            if not is_square(h(Z_cand)):
                continue
            # Criterion 4:
            #   At least one of g(Z) and g(-Z / 2) is square in F.
            if is_square(g(Z_cand)) or is_square(g(-Z_cand / F(2))):
                return Z_cand
        ctr += 1

# Justify the given element is quadratic non-residue in the field
def is_quad_non_res(n):
    if kronecker(n, p) == -1:
        print(f"{n} is quadratic non-residue.")
    else:
        print(f"{n} is not quadratic non-residue.")

# Given an integer with 256 bits in hex, convert it into 4 limbs of 64 bits where the least significent limb is put first.
def u_64_little_endian(n):
    str_hex = n
    str_hex_without_0x = str_hex[2:]
    # pad 0s into hex litteral of 64 digits for the 256 bits 
    full_width_str = '0' * (64 - len(str_hex_without_0x)) + str_hex_without_0x
    assert len(full_width_str) == 64
    res = []
    # divide the litteral into 4 limbs of 64 bits, the least significent limb is put first
    for i in range(4):
        temp = '0x' + full_width_str[64 - 16 * (i + 1) : 64 - 16 * i]
        res.append(temp)
    return res

# Output a rust-friendly form of 4 limbs representation for the field element:
# F::from_raw([
# 0x1234567890123456,
# 0x1234567890123456,
# 0x1234567890123456,
# 0x1234567890123456,
# ]),
def print_for_rust(elem):
    print('Base::from_raw([')
    for limb in u_64_little_endian(elem):
        print(limb + ",")
    print(']),')

is_quad_non_res(7)
is_quad_non_res(ED_d)
jubjub_z = find_z_svdw(Fp, WEI_A, WEI_B)
print_for_rust(hex(jubjub_z))
print_for_rust(hex(WEI_A))
print_for_rust(hex(WEI_B))