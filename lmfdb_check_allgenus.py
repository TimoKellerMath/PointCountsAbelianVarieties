from lmfdb import db

qs = [2,3,4,5,7,8,9,11,13,16,17,19,23,25]

for g in range(2,7):
  for q in qs:
    query = {'g': g, 'q' : q}
    abvars = list(db.av_fq_isog.search(query))
    N = len(abvars)
    if N == 0:
      continue
    distinct_npointcounttuples = []
    isinjective_npointcounttuples = []
    for n in range(g,g+1):    # only interested in considering all g point counts; no fewer
    # for n in range(1,g+1):    # considering n point counts, for any n <= g
      npointcounts = set()
      for x in abvars:
        ptcounts = x['abvar_counts']
        npointcounts.add(tuple(ptcounts[i] for i in range(n)))

      distinct_npointcounttuples.append(len(npointcounts))
      boo = len(npointcounts) == N
      isinjective_npointcounttuples.append(boo)

    print(g,q,N,isinjective_npointcounttuples,distinct_npointcounttuples)


# 2 2 35 [True] [35]
# 2 3 63 [True] [63]
# 2 4 91 [True] [91]
# 2 5 129 [True] [129]
# 2 7 207 [True] [207]
# 2 8 167 [True] [167]
# 2 9 285 [True] [285]
# 2 11 401 [True] [401]
# 2 13 513 [True] [513]
# 2 16 457 [True] [457]
# 2 17 765 [True] [765]
# 2 19 897 [True] [897]
# 2 23 1193 [True] [1193]
# 2 25 1273 [True] [1273]

# 3 2 215 [True] [215]
# 3 3 677 [True] [677]
# 3 4 1397 [True] [1397]
# 3 5 2953 [True] [2953]
# 3 7 7979 [True] [7979]
# 3 8 7623 [True] [7623]
# 3 9 15459 [True] [15459]
# 3 11 30543 [True] [30543]
# 3 13 50371 [True] [50371]
# 3 16 59535 [True] [59535]
# 3 17 112283 [True] [112283]
# 3 19 156589 [True] [156589]
# 3 23 277517 [True] [277517]
# 3 25 332166 [True] [332166]

# 4 2 1645 [True] [1645]
# 4 3 10963 [True] [10963]
# 4 4 38160 [True] [38160]
# 4 5 132839 [True] [132839]

# 5 2 14325 [True] [14325]
# 5 3 267465 [True] [267465]

# 6 2 164937 [True] [164937]

##############################
# Full data

# 2 2 35 [False, True] [19, 35]
# 2 3 63 [False, True] [34, 63]
# 2 4 91 [False, True] [52, 91]
# 2 5 129 [False, True] [68, 129]
# 2 7 207 [False, True] [108, 207]
# 2 8 167 [False, True] [111, 167]
# 2 9 285 [False, True] [155, 285]
# 2 11 401 [False, True] [206, 401]
# 2 13 513 [False, True] [264, 513]
# 2 16 457 [False, True] [305, 457]
# 2 17 765 [False, True] [390, 765]
# 2 19 897 [False, True] [456, 897]
# 2 23 1193 [False, True] [604, 1193]
# 2 25 1273 [False, True] [673, 1273]

# 3 2 215 [False, False, True] [63, 183, 215]
# 3 3 677 [False, False, True] [156, 607, 677]
# 3 4 1397 [False, False, True] [305, 1315, 1397]
# 3 5 2953 [False, False, True] [503, 2805, 2953]
# 3 7 7979 [False, False, True] [1121, 7795, 7979]
# 3 8 7623 [False, False, True] [1406, 7573, 7623]
# 3 9 15459 [False, False, True] [2053, 15335, 15459]
# 3 11 30543 [False, False, True] [3357, 30451, 30543]
# 3 13 50371 [False, False, True] [5067, 50353, 50371]
# 3 16 59535 [False, True, True] [7858, 59535, 59535]
# 3 17 112283 [False, True, True] [9843, 112283, 112283]
# 3 19 156589 [False, True, True] [12975, 156589, 156589]
# 3 23 277517 [False, True, True] [20876, 277517, 277517]
# 3 25 332166 [False, True, True] [25556, 332166, 332166]

# 4 2 1645 [False, False, False, True] [205, 1050, 1643, 1645]
# 4 3 10963 [False, False, False, True] [732, 7349, 10962, 10963]
# 4 4 38160 [False, False, False, True] [1862, 28542, 38157, 38160]
# 4 5 132839 [False, False, True, True] [3885, 97485, 132839, 132839]

# 5 2 14325 [False, False, False, True, True] [658, 6050, 14271, 14325, 14325]
# 5 3 267465 [False, False, False, True, True] [3519, 100423, 267426, 267465, 267465]

# 6 2 164937 [False, False, False, True, True, True] [2155, 36777, 163567, 164937, 164937, 164937]



