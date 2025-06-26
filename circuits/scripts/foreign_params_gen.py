'''
This file is designed to optimize the parameters for implementing foreign-field
modular arithmetic on a SNARK circuit, where the cost is measured in number of
rows.

A big integer is represented in base B as a vector of n limbs of size at most B.
For example, [x_{n-1}, ..., x_1, x_0] represents integer (1 + sum_i B^i x_i).

We assume a range-check mechanism for checking membership in the range
[0,2^t) for any integer t.

Notation:
 - p : native SNARK modulus (scalar field order)
 - q : non-native emulated modulus
 - B : base of the limbs-representation
 - n : number of limbs necessary to represent a Zq integer: ceil(log_B(q))
'''

import sys
from math import ceil, log, gcd

# The number of parallel lookups that we support in one row.
NB_PARALLEL_LOOKUPS = 4

DEBUG = "--debug" in sys.argv

VALID_PARAMETERS = "valid"
NOT_ENOUGH_MODULI = "not_enough_moduli"
INVALID_AUX_MODULUS = "invalid_aux_modulus"

def lcm(l):
    acc = 1
    for x in l:
        acc = abs(acc * x) // gcd(acc, x)
    return acc

# The number of bits of a power of 2
def log2(n):
    k = len(bin(n-1)) - 2
    assert(2**k == n)
    return k

def next_cheapest_power_of_2(MAX_BIT_LEN, x):
    best_log = len(bin(x-1)) - 2
    best = cost_range_check(MAX_BIT_LEN, best_log)
    for i in range(1, 100):
        cost = cost_range_check(MAX_BIT_LEN, best_log + i)
        if cost < best:
            best = cost
            best_log = best_log + i
    return 2**best_log

def mul_expr_bounds(q, n, B, base_powers, double_base_powers):
    # Note that x := 1 + sum_i base^i x_i, and that y, z are defined
    # analogously.
    #
    # We enforce x * y - z = 0 (mod m) with the equation:
    #  sum_xy + sum_x + sum_y - sum_z = k * m
    #
    # where
    #  sum_xy := sum_i (sum_j (base^{i+j} % m) * x_i * y_j),
    #   sum_x := sum_i (base^i % m) * x_i ,
    #   sum_y := sum_i (base^i % m) * y_i ,
    #   sum_z := sum_i (base^i % m) * z_i .
    #
    # Let max_sum_xy (resp. max_sum_x, etc) be the maximum value that sum_xy
    # (resp. sum_x, etc) can take, i.e. when replacing x_i, y_i (resp. z_i)
    # by (base-1).

    max_sum_xy = (B-1)**2 * sum(double_base_powers)
    max_sum_x = (B-1) * sum(base_powers)
    max_sum_y = max_sum_x
    max_sum_z = max_sum_x

    expr_min = -max_sum_z
    expr_max = max_sum_xy + max_sum_x + max_sum_y

    return (expr_min, expr_max)

def tangent_expr_bounds(q, n, B, base_powers, double_base_powers):
    # Recall that limbs x_i represent integer 1 + sum_i base^i x_i.
    # Let px := 1 + sum_i base^i px_i
    #     py := 1 + sum_i base^i py_i
    # lambda := 1 + sum_i base^i lambda_i
    #
    # We will have a custom gate enforcing equation:
    #   3 * px^2 + a = 2 * py * lambda  (mod m)
    #
    # Define:
    #      sum_px := sum_i (base^i % m) * px_i
    #      sum_py := sum_i (base^i % m) * py_i
    #  sum_lambda := sum_i (base^i % m) * lambda_i
    #     sum_px2 := sum_i (sum_j (base^{i+j} % m) * px_i * px_j)
    #     sum_lpy := sum_i (sum_j (base^{i+j} % m) * lambda_i * py_j)
    #
    # We enforce relation (we assume a = 0):
    #    3 * (1 + sum_px) * (1 + sum_px)
    #  = 2 * (1 + sum_py) * (1 + sum_lambda)  (mod m)
    #
    # Thus, expr is
    #   3 * (2 * sum_px + sum_px2) + 1
    # - 2 * (sum_py + sum_lambda + sum_lpy)

    max_sum_px = (B-1) * sum(base_powers)
    max_sum_py = max_sum_px
    max_sum_lambda = max_sum_px
    max_sum_px2 = (B-1)**2 * sum(double_base_powers)
    max_sum_lpy = max_sum_px2
    expr_min = - 2 * (max_sum_py + max_sum_lambda + max_sum_lpy) + 1
    expr_max = 3 * (max_sum_px + max_sum_px + max_sum_px2) + 1

    return (expr_min, expr_max)

def lambda2_expr_bounds(q, n, B, base_powers, double_base_powers):
    # Recall that limbs x_i represent emulated field element 1 + sum_i base^i x_i.
    # Let px := 1 + sum_i base^i px_i
    #     qx := 1 + sum_i base^i qx_i
    #     rx := 1 + sum_i base^i rx_i
    #  lamda := 1 + sum_i base^i lambda_i
    #
    # We will have a custom gate enforcing equation:
    #  px + qx + rx = lambda^2   (mod m)
    #
    # Define:
    #      sum_px := sum_i (base^i % m) * px_i
    #      sum_qx := sum_i (base^i % m) * qx_i
    #      sum_rx := sum_i (base^i % m) * rx_i
    #  sum_lambda := sum_i (base^i % m) * lambda_i
    # sum_lambda2 := sum_i (sum_j (base^{i+j} % m) * lambda_i * lambda_j)
    #
    # We enforce:
    #  (1 + sum_px) + (1 + sum_qx) + (1 + sum_rx)
    #    - (1 + 2 sum_lambda + sum_lambda2) = k * m
    #
    # Thus, expr is
    #  2 + sum_px + sum_qx + sum_rx - (2 sum_lambda + sum_lambda2)

    max_sum_px = (B-1) * sum(base_powers)
    max_sum_qx = max_sum_px
    max_sum_rx = max_sum_px
    max_sum_lambda = max_sum_px
    max_sum_lambda2 = (B-1)**2 * sum(double_base_powers)

    expr_min = 2 - (2 * max_sum_lambda + max_sum_lambda2)
    expr_max = 2 + max_sum_px + max_sum_qx + max_sum_rx

    return (expr_min, expr_max)


def slope_expr_bounds(q, n, B, base_powers, double_base_powers):
    # Recall that limbs x_i represent emulated field element 1 + sum_i base^i x_i.
    # Let px := 1 + sum_i base^i px_i
    #     py := 1 + sum_i base^i py_i
    #     qx := 1 + sum_i base^i qx_i
    #     qy := 1 + sum_i base^i qy_i
    # lambda := 1 + sum_i base^i lambda_i
    #
    # We will have a custom gate enforcing equation:
    #  ± qy - py = lambda * (qx - px)   (mod m)
    #
    # This asserts that the slope between points (qx, ±qy) and (px, py) is lambda.
    # If the two points are equal, this condition becomes trivial.
    #
    # Define:
    #      sum_px := sum_i (base^i % m) * px_i
    #      sum_py := sum_i (base^i % m) * py_i
    #      sum_qx := sum_i (base^i % m) * qx_i
    #      sum_qy := sum_i (base^i % m) * qy_i
    #  sum_lambda := sum_i (base^i % m) * lambda_i
    #     sum_lpx := sum_i (sum_j (base^{i+j} % m) * lambda_i * px_j)
    #     sum_lqx := sum_i (sum_j (base^{i+j} % m) * lambda_i * qx_j)
    #        sign in {-1, 1}
    #
    # We enforce:
    #  sign * (1 + sum_qy) - (1 + sum_py)
    #   - (1 + sum_lambda) * ((1 + sum_qx) - (1 + sum_px)) = k * m
    #
    # Thus, expr is:
    #  sign - 1 + sign * sum_qy - sum_py
    #    - sum_qx + sum_px - sum_lqx + sum_lpx
    max_sum_px = (B-1) * sum(base_powers)
    max_sum_py = max_sum_px
    max_sum_qx = max_sum_px
    max_sum_qy = max_sum_px
    max_sum_lpx = (B-1)**2 * sum(double_base_powers)
    max_sum_lqx = max_sum_lpx

    expr_min = -(2 + max_sum_qy + max_sum_py + max_sum_qx + max_sum_lqx)
    expr_max = max_sum_qy + max_sum_px + max_sum_lpx

    return (expr_min, expr_max)


class Params:
    def __init__(self, p, q, B, auxiliary_moduli, RC_len,
                 expr_bounds, double_base_powers = None):
        n = ceil(log(q) / log(B))
        self.p = p
        self.q = q
        self.B = B
        self.n = n
        self.auxiliary_moduli = auxiliary_moduli
        self.validity = VALID_PARAMETERS

        base_powers = [B**i % q for i in range(n)]

        if double_base_powers == None:
            double_base_powers = [B**(i+j) % q for i in range(n) for j in range(n)]

        (expr_min, expr_max) = expr_bounds(q, n, B, base_powers, double_base_powers)

        # We can bound the value of k in the range [k_min, k_max], where:
        assert (expr_min < 0)
        k_min = - (abs(expr_min) // q)
        k_max = expr_max // q

        # By defining u := k - k_min, we can now restrict u in the range
        # [0, u_max) (for any u_max > k_max - k_min), a constraint that can be
        # enforced through range-checks if u_max is a power of 2.
        u_max = next_cheapest_power_of_2(RC_len, k_max - k_min + 1)
        self.k_min = k_min
        self.u_max = u_max

        # Now, assuming u is restricted in [0, u_max), we will bound the amount:
        #  expr - (u + k_min) * q

        lcm_lower_bound = expr_min - (u_max + k_min) * q
        lcm_upper_bound = expr_max - k_min * q
        lcm_threshold = max(-lcm_lower_bound, lcm_upper_bound)

        if lcm(auxiliary_moduli) <= lcm_threshold:
            if DEBUG:
                print("You must consider more auxiliary moduli:")
                print("  lcm_threshold:", lcm_threshold)
                print("  lcm(auxiliary_moduli):   ", lcm(auxiliary_moduli))
                print("About another %d bits to go" % int(log(lcm_threshold/lcm(auxiliary_moduli)) / log(2)))
            self.validity = NOT_ENOUGH_MODULI

        self.ls_min = []
        self.vs_max = []

        for mj in auxiliary_moduli:
            if mj == p:
                continue

            bi_mod_q_mod_mj = [(B**i % q) % mj for i in range(n)]
            bij_mod_q_mod_mj = [b % mj for b in double_base_powers]

            # In order to enforce the above equation modulo lcm(M), we need to
            # enforce the following equation for every mj in M:
            #
            #  expr_mj - u * (q % mj) - (k_min * q) % mj = lj * mj ,
            #
            # with the exception of the native modulus, p, for which we check:
            #  expr - (u + k_min) * q =_p 0 .
            #
            # For the rest of moduli, we can bound the auxiliary variable lj in
            # the interval [lj_min, lj_max] as follows.

            (expr_mj_min, expr_mj_max) = expr_bounds(q, n, B, bi_mod_q_mod_mj, bij_mod_q_mod_mj)

            lj_min = - (abs(expr_mj_min - u_max * (q % mj) - (k_min * q) % mj ) // mj)
            lj_max = (expr_mj_max - (k_min * q) % mj ) // mj

            # As before, by defining vj := lj - lj_min, vj can be restricted
            # in the range [0, vj_max), (for any vj_max > lj_max - lj_min).

            vj_max = next_cheapest_power_of_2(RC_len, lj_max - lj_min + 1)

            self.ls_min.append(lj_min)
            self.vs_max.append(vj_max)

            # Now, assuming vj is restricted in [0, vj_max), we will bound:
            #  sum_xy_mj + sum_x_mj + sum_y_mj - sum_z_mj - u * (q % mj)
            #   - (k_min * q) % mj - (vj + lj_min) * mj

            lower_bound = expr_mj_min - u_max * (q % mj) - (k_min * q) % mj - (vj_max + lj_min) * mj
            upper_bound = expr_mj_max - (k_min * q) % mj - lj_min * mj
            p_threshold = max(-lower_bound, upper_bound)

            if p <= p_threshold:
                self.validity = INVALID_AUX_MODULUS
                if DEBUG:
                    print("Auxiliary modulus %d is not valid (there will be wrap-around)" % mj)
                    print("     bij_q_mj:", bij_mod_q_mod_mj)
                    print("      bi_q_mj:", bi_mod_q_mod_mj)
                    print("        u_max:", u_max)
                    print("            l: [%d, %d]" % (lj_min, lj_max))
                    print("       vj_max:", vj_max)
                    print("  lower_bound:", lower_bound)
                    print("  upper_bound:", upper_bound)
                    print("  p_threshold:", p_threshold)
                    print("Threshold violated by about %d bits" % int(log(p_threshold/p) / log(2)))


Tables = {}

# The cost in number of rows of range-checking a value in the range [0, 2^n)
# with our current decomposition chip, instantiated with MAX_BIT_LEN.
def cost_range_check(MAX_BIT_LEN, n):
    global Tables

    if Tables.get(MAX_BIT_LEN) == None:
        Tables[MAX_BIT_LEN] = {}

    # base case
    if n == 0:
        return 0

    T = Tables.get(MAX_BIT_LEN)
    if T.get(n) != None:
        return T.get(n)

    best = n   # An upper bound on the optimum
    for nb_cols in range(1, NB_PARALLEL_LOOKUPS+1):
        for bit_len in range(1, MAX_BIT_LEN+1):
            next_n = n - nb_cols * bit_len
            if next_n < 0:
                continue

            sol = cost_range_check(MAX_BIT_LEN, next_n)
            if sol < best:
                best = sol

    T[n] = best + 1
    return best + 1

# The cost in rows of implementing FFA.mul with the given params
def cost_mul(RC_len, params):
    # We place the mul identity in 2 rows
    cost = 2

    # Consider the range-checks per limb wrt the base
    cost += params.n * cost_range_check(RC_len, log2(params.B))

    # Consider the range-check of u
    cost += cost_range_check(RC_len, log2(params.u_max))

    # Consider the range-checks of vj
    cost += sum([cost_range_check(RC_len, log2(vj)) for vj in params.vs_max])

    return cost

# The cost in rows of implementing tangent assertion with the given params.
def cost_tangent(RC_len, params):
    # We place the mul identity in 2 rows
    cost = 2

    # Consider the range-check of u
    cost += cost_range_check(RC_len, log2(params.u_max))

    # Consider the range-checks of vj
    cost += sum([cost_range_check(RC_len, log2(vj)) for vj in params.vs_max])

    return cost

# The cost in rows of implementing tangent assertion with the given params.
def cost_lambda2(RC_len, params):
    # We place the mul identity in 3 rows
    cost = 3

    # Consider the range-check of u
    cost += cost_range_check(RC_len, log2(params.u_max))

    # Consider the range-checks of vj
    cost += sum([cost_range_check(RC_len, log2(vj)) for vj in params.vs_max])

    return cost

# The cost in rows of implementing tangent assertion with the given params.
def cost_slope(RC_len, params):
    # We place the mul identity in 3 rows
    cost = 3

    # Consider the range-check of u
    cost += cost_range_check(RC_len, log2(params.u_max))

    # Consider the range-checks of vj
    cost += sum([cost_range_check(RC_len, log2(vj)) for vj in params.vs_max])

    return cost

# The cost in rows of implementing incomplete point addition with the given parameters.
def cost_incomplete_point_add(B, n, RC_len, lambda2_cost, slope_cost):
    cost_assign = n * cost_range_check(RC_len, log2(B))
    cost_assign_point = 1 + 2 * cost_assign
    cost_incomplete_add = cost_assign_point + cost_assign + lambda2_cost + 2 * slope_cost

    return cost_incomplete_add

# The cost in rows of implementing scalar_mul with windows of size WS with the
# given parameters.
def cost_scalar_mul(B, n, WS, RC_len, norm_cost, lambda2_cost, slope_cost, tangent_cost):
    # Cost of assign r:
    nb_assign = 1

    # Cost of computing α:
    nb_incomplete_add = 1
    nb_double = 1

    # Cost of negate α:
    nb_negate = 1

    # Cost of computing the table: [-α, p-α, 2p-α, 3p-α, ..., (2^WS-1)p-α]
    nb_incomplete_assert_different_x = 2**WS - 1
    nb_incomplete_add += 2**WS - 1
    nb_multi_select = 2**WS

    # Double-and-add loop
    nb_iterations = ceil(256 / WS)
    nb_double += 256
    nb_incomplete_add += nb_iterations
    nb_incomplete_assert_different_x += nb_iterations
    nb_multi_select += nb_iterations

    # Negate r_correction:
    nb_negate += 1

    # Complete add correction:
    nb_incomplete_add += 1

    cost_assign = n * cost_range_check(RC_len, log2(B))
    cost_assign_point = 1 + 2 * cost_assign
    cost_negate = n + norm_cost
    cost_incomplete_add = cost_assign_point + cost_assign + lambda2_cost + 2 * slope_cost
    cost_double = cost_assign_point + 1 + cost_assign + tangent_cost + lambda2_cost + slope_cost
    cost_incomplete_assert_different_x = 4
    cost_multi_select = 1

    cost = 0
    cost += cost_assign * nb_assign
    cost += cost_negate * nb_negate
    cost += cost_incomplete_add * nb_incomplete_add
    cost += cost_double * nb_double
    cost += cost_incomplete_assert_different_x * nb_incomplete_assert_different_x
    cost += cost_multi_select * nb_multi_select

    return cost

# p is the native modulus, q is the emulated one
def optimization_round(p, q, RC_len, nb_limbs, expr_bounds):

    nb_bits = ceil(log(q) / log(2))
    log2_B = min([k for k in range(nb_bits) if 2**(k * nb_limbs) >= q])
    B = next_cheapest_power_of_2(RC_len, 2**log2_B)

    auxiliary_moduli = [p]
    params = Params(p, q, B, auxiliary_moduli, RC_len, expr_bounds)
    if params.validity == VALID_PARAMETERS:
        return (params, ['native'])

    # Figure out what maximum power of two as an auxiliary modulus we can use
    log2_m = 0
    for k in range(1, nb_bits):
        params = Params(p, q, B, [2**k], RC_len, expr_bounds)
        if params.validity == INVALID_AUX_MODULUS:
            break
        log2_m = k

    if log2_m == 0:
        return None

    m = 2**log2_m
    auxiliary_moduli = [p, m]
    auxiliary_moduli_str = ['native', '2^' + str(log2_m)]

    params = Params(p, q, B, auxiliary_moduli, RC_len, expr_bounds)

    i = 1
    while params.validity != VALID_PARAMETERS:
        params = Params(p, q, B, auxiliary_moduli + [m - i],
                        RC_len, expr_bounds)
        if params.validity != INVALID_AUX_MODULUS:
            auxiliary_moduli += [m - i]
            auxiliary_moduli_str += ['2^' + str(log2_m) + '-' + str(i)]
        i += 1

    return (params, auxiliary_moduli_str)

def pp_params(params, RC_len, auxiliary_moduli_str):
    assert (params.validity == VALID_PARAMETERS)
    log2_B = int(log(params.B) / log(2))
    moduli = ", ".join(auxiliary_moduli_str)
    info = "B = 2^%d, nb_limbs = %d, moduli = {%s}" % (log2_B, params.n, moduli)
    info += ", u_max = {%d}" % log2(params.u_max)
    info += ", vs_max = {[%s]}" % str([log2(v) for v in params.vs_max])
    info += ", MAX_BIT_LEN = %d" % RC_len
    return info


# p is the native modulus, q is the emulated one
def optimize(p, q):
    # We minimize tangent_expr_bounds, typically the bottleneck
    expr_bounds = tangent_expr_bounds

    for nb_limbs in range(2, 8):
      best_cost = 2**31 # A large number, reset the best on every nb_limbs
      print()
      for RC_len in range(8, 20+1):
          opt = optimization_round(p, q, RC_len, nb_limbs, expr_bounds)
          if opt == None:
              continue

          (params, auxiliary_moduli_str) = opt
          tangent_cost = cost_tangent(RC_len, params)

          params_mul = Params(p, q, params.B, params.auxiliary_moduli, RC_len, mul_expr_bounds)
          mul_cost = cost_mul(RC_len, params)

          params_lambda2 = Params(p, q, params.B, params.auxiliary_moduli, RC_len, lambda2_expr_bounds)
          lambda2_cost = cost_lambda2(RC_len, params)

          params_slope = Params(p, q, params.B, params.auxiliary_moduli, RC_len, slope_expr_bounds)
          slope_cost = cost_slope(RC_len, params)

          norm_cost = mul_cost # This is an upper bound for the cost of normalization

          # Let's optimize the cost of incomplete point addition, the dominant factor in an msm
          cost = cost_incomplete_point_add(params.B, params.n, RC_len, lambda2_cost, slope_cost)

          if cost <= best_cost:
              best_cost = cost
              info = pp_params(params, RC_len, auxiliary_moduli_str)
              print("%d (incomplete_add) | %d (mul) | %d (slope) | %d (λ²) | %d (tangent) \t%s" %
                    (cost, mul_cost, slope_cost, lambda2_cost, tangent_cost, info))

PLUTO_SCALAR = 0x24000000000024000130e0000d7f70e4a803ca76f439266f443f9a5c7a8a6c7be4a775fe8e177fd69ca7e85d60050af41ffffcd300000001
ERIS_SCALAR = 0x24000000000024000130e0000d7f70e4a803ca76f439266f443f9a5cda8a6c7be4a7a5fe8fadffd6a2a7e8c30006b9459ffffcd300000001
ORDERS = {
    'secp256k1-base' : 2**256 - 2**32 - 2**9 - 2**8 - 2**7 - 2**6 - 2**4 - 1,
    'secp256k1-scalar' : 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141,
    'pluto-base' : ERIS_SCALAR,
    'pluto-scalar' : PLUTO_SCALAR,
    'eris-scalar' : ERIS_SCALAR,
    'bn254-base' : 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47,
    'bn254-scalar' : 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001,
    'bls12-381-base': 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab,
    'bls12-381-scalar': 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001,
}

def parse_modulus(m):
    fetched = ORDERS.get(m)
    if fetched != None:
        return fetched

    return eval(m)


if __name__ == '__main__':
    if len(sys.argv) < 3:
        keys = "\n".join([" - " + k for k in ORDERS.keys()])
        sys.exit("Usage: python3 foreign_params_gen.py NATIVE EMULATED\n"\
                 "Where NATIVE and EMULATED must be replaced by concrete constants or "\
                 "one of the following supported values:\n" + keys)

    p = parse_modulus(sys.argv[1])
    q = parse_modulus(sys.argv[2])

    print("Optimizing parameters for:\n   Native modulus: %d\n Emulated modulus: %d" % (p, q))
    optimize(p, q)
