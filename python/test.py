import fuzzysat
import fuzzysat.z3 as z3

def print_sat_info(r):
    is_sat, is_opt_sat, proof = r
    if is_sat:
        print("SAT: %s" % proof)
    elif is_opt_sat:
        print("OPTSAT: %s" % proof)
    else:
        print("UNKNOWN")

s = fuzzysat.FuzzySolver(
    seed=b"\x00\x00\x00\x01")

inp = z3.Concat(
    s.get_input(0),
    s.get_input(1),
    s.get_input(2),
    s.get_input(3))

s.add(inp < 16)
s.add(inp > 0)

print("checking %s" % (inp > 10))
r = s.check_sat(inp > 10)
print_sat_info(r)

print("checking %s" % (inp > 20))
r = s.check_sat(inp > 20)
print_sat_info(r)

print()

print("eval_upto (all):   ")
for val, proof in s.eval_upto(inp, 20):
    print("   ", val, proof)
print()
print("eval_upto (greedy):   ")
for val, proof in s.eval_upto_inner(inp, 20, mode="greedy"):
    print("   ", val, proof)
print()
print("eval_upto (gd to min):")
for val, proof in s.eval_upto_inner(inp, 20, mode="gd_min"):
    print("   ", val, proof)
print()
print("eval_upto (gd to max):")
for val, proof in s.eval_upto_inner(inp, 20, mode="gd_max"):
    print("   ", val, proof)

print()

minval, minproof = s.minimize(inp)
maxval, maxproof = s.maximize(inp)

print("minval:", minval, "(", str(minproof), ")")
print("maxval:", maxval, "(", str(maxproof), ")")
