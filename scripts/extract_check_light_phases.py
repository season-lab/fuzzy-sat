import tabulate
import sys
import re

if len(sys.argv) < 2:
	print("error: not enough arguments")
	sys.exit(1)

print_csv = False
if len(sys.argv) > 2:
	print_csv = True

filename = sys.argv[1]
fin = open(filename, "r")

hist = {}
def add_or_inc(hist, v):
	if v in hist:
		hist[v] += 1
	else:
		hist[v] = 1

for line in fin:
	match = re.findall(r"\[check light .*\]", line) 
	if len(match) == 0:
		continue
	assert len(match) == 1
	m = match[0]
	add_or_inc(hist, m.replace("[check light ", "").replace("]", ""))

sorted_keys = sorted(hist, key=lambda x: hist[x], reverse=True)

table = []
for key in sorted_keys:
	table.append([key, hist[key]])

if not print_csv:
	print(tabulate.tabulate(table, headers=["transformation", "num"]))
else:
	for line in table:
		print(';'.join(map(str, line)))

fin.close()
