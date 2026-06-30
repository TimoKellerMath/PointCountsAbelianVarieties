from lmfdb import db

query = {
    'g': 3,
    'q' : 17
}
abvars = list(db.av_fq_isog.search(query))
len(abvars)
# 112283

pointcounts1 = set()
pointcounts2 = set()
pointcounts3 = set()
for x in abvars:
  ptcounts = x['abvar_counts']
  pointcounts1.add(ptcounts[0])
  pointcounts2.add((ptcounts[0],ptcounts[1]))
  pointcounts3.add((ptcounts[0],ptcounts[1],ptcounts[2]))

len(pointcounts1)
len(pointcounts2)
len(pointcounts3)

# 9843
# 112283
# 112283

###########################################################
from lmfdb import db

g = 3
qs = [2,3,4,5,7,8,9,11,13,16,17,19,23,25]
for q in qs:
  query = {
      'g': g,
      'q' : q
  }
  abvars = list(db.av_fq_isog.search(query))
  N = len(abvars)

  pointcounts1 = set()
  pointcounts2 = set()
  pointcounts3 = set()
  for x in abvars:
    ptcounts = x['abvar_counts']
    pointcounts1.add(ptcounts[0])
    pointcounts2.add((ptcounts[0],ptcounts[1]))
    pointcounts3.add((ptcounts[0],ptcounts[1],ptcounts[2]))

  boo1 = len(pointcounts1) == N
  boo2 = len(pointcounts2) == N
  boo3 = len(pointcounts3) == N
  print(g,q,N,boo1,boo2,boo3)

# 3 2 215 False False True
# 3 3 677 False False True
# 3 4 1397 False False True
# 3 5 2953 False False True
# 3 7 7979 False False True
# 3 8 7623 False False True
# 3 9 15459 False False True
# 3 11 30543 False False True
# 3 13 50371 False False True
# 3 16 59535 False True True
# 3 17 112283 False True True
# 3 19 156589 False True True
# 3 23 277517 False True True
# 3 25 332166 False True True


###########################################################
