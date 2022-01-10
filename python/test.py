import fuzzysat
import fuzzysat.z3 as z3

s = fuzzysat.FuzzySolver(b"\x00\x00\x00\x00")

inp = z3.Concat(
    z3.BitVec(0, 8),
    z3.BitVec(1, 8),
    z3.BitVec(2, 8),
    z3.BitVec(3, 8))

s.add(inp < 16)
s.add(inp > 0)
is_sat, proof = s.check_sat(inp > 10)

if is_sat:
    print("SAT: %s" % str(proof))
else:
    print("UNKNOWN")

print(s.eval_upto(inp, 20))
print(s.eval_upto(inp, 20, use_gd=True, gd_to_max=False))
print(s.eval_upto(inp, 20, use_gd=True, gd_to_max=True))
