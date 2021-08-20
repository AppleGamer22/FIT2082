#!/usr/bin/python

## Original format:
### type octile
### height <h>
### width <w>
### map
### @@@@@@@@@TTTTTTT........TTTTTT@@@@@@
## where:
## - @: impassable
## - T: impassable (tree)
## - .: reachable
## Because of the way the ECBS implementation is set up,
## we need to pad the graph with an impassable ring.
def convert_map(src, dest):
  header = src.readline().strip()
  if header.startswith("type"):
    ht = int(src.readline().strip().split()[1])
    wd = int(src.readline().strip().split()[1])
    src.readline()
  else:
    toks = header.split(',')
    ht = int(toks[0])
    wd = int(toks[1])

  print >>dest, "{0},{1}".format(ht+2, wd+2)

  print >>dest, ",".join(["1" for i in xrange(wd+2)])
  for r in xrange(ht):
    row = src.readline().strip()
    prow = ["1"] + map(lambda e : "0" if e == '.' else "1", row) + ["1"] 
    assert(len(prow) == wd+2)
    print >>dest, ",".join(prow)
  print >>dest, ",".join(["1" for i in xrange(wd+2)])

if __name__ == '__main__':
  import sys

  convert_map(sys.stdin, sys.stdout) 
