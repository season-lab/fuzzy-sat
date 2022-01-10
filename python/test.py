import fuzzysat
import fuzzysat.z3 as z3

s = fuzzysat.FuzzySolver(b"\x00\x00\x00\x00")

inp = z3.Concat(
    s.get_input(0),
    s.get_input(1),
    s.get_input(2),
    s.get_input(3))

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
