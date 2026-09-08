## 25/02/2026

### secrecy.sp

**Command:**
```
/usr/bin/time -f '\t%E real,\t%U user,\t%S sys,\t%K amem,\t%M mmem' squirrel secrecy.sp 
```

**Without reset:**
```
[completion.ml] complete:
  775 entries
[completion.ml] unify:
  139193 live entries (total: 139193)
[completion.ml] normalization:
  132433 live entries (total: 132433)
[utils.ml] union_find_classes:
  0 live entries (total: 0)
[match.ml] to_subst_locals:
  1688 live entries (total: 1688)
[constr.ml] build models:
  7307 live entries (total: 7307)
[constr.ml] get classes:
  1223120 live entries (total: 1223120)
[utils.ml] union_find_classes:
  171024 live entries (total: 171024)
Goodbye!
	5:41.91 real,	412.12 user,	17.95 sys,	0 amem,	12 049 436 mmem
```

**With reset:**
```
[completion.ml] complete:
  1 entries
[completion.ml] unify:
  1 live entries (total: 1)
[completion.ml] normalization:
  4 live entries (total: 4)
[utils.ml] union_find_classes:
  0 live entries (total: 0)
[match.ml] to_subst_locals:
  0 live entries (total: 0)
[constr.ml] build models:
  31 live entries (total: 31)
[constr.ml] get classes:
  297 live entries (total: 297)
[utils.ml] union_find_classes:
  122 live entries (total: 122)
Goodbye!
	5:44.88 real,	423.83 user,	18.94 sys,	0 amem,	10 112 872 mmem
```

**With reset and no history:** (more memory usage?!)
```
[completion.ml] complete:
  1 entries
[completion.ml] unify:
  1 live entries (total: 1)
[completion.ml] normalization:
  4 live entries (total: 4)
[utils.ml] union_find_classes:
  0 live entries (total: 0)
[match.ml] to_subst_locals:
  0 live entries (total: 0)
[constr.ml] build models:
  31 live entries (total: 31)
[constr.ml] get classes:
  297 live entries (total: 297)
[utils.ml] union_find_classes:
  122 live entries (total: 122)
Goodbye!
	5:37.65 real,	409.60 user,	18.68 sys,	0 amem,	12 076 472 mmem
```

### simulation.sp

**Command:**
```
/usr/bin/time -f '\t%E real,\t%U user,\t%S sys,\t%K amem,\t%M mmem' squirrel simulation.sp 
```

**Without reset:**
```
[completion.ml] complete:
  217 entries
[completion.ml] unify:
  8559 live entries (total: 9527)
[completion.ml] normalization:
  4002 live entries (total: 5590)
[utils.ml] union_find_classes:
  0 live entries (total: 0)
[match.ml] to_subst_locals:
  0 live entries (total: 136)
[constr.ml] build models:
  12 live entries (total: 316)
[constr.ml] get classes:
  88 live entries (total: 5530)
[utils.ml] union_find_classes:
  28 live entries (total: 296)
Goodbye!
	0:21.67 real,	31.31 user,	1.83 sys,	0 amem,	681 416 mmem
```

**With reset:**
```
[completion.ml] complete:
  1 entries
[completion.ml] unify:
  9 live entries (total: 9)
[completion.ml] normalization:
  11 live entries (total: 11)
[utils.ml] union_find_classes:
  0 live entries (total: 0)
[match.ml] to_subst_locals:
  0 live entries (total: 0)
[constr.ml] build models:
  6 live entries (total: 6)
[constr.ml] get classes:
  44 live entries (total: 44)
[utils.ml] union_find_classes:
  14 live entries (total: 14)
Goodbye!
	0:21.49 real,	31.56 user,	1.83 sys,	0 amem,	667 796 mmem

```

**With reset and no history:**
```
[completion.ml] complete:
  1 entries
[completion.ml] unify:
  9 live entries (total: 9)
[completion.ml] normalization:
  11 live entries (total: 11)
[utils.ml] union_find_classes:
  0 live entries (total: 0)
[match.ml] to_subst_locals:
  0 live entries (total: 0)
[constr.ml] build models:
  6 live entries (total: 6)
[constr.ml] get classes:
  44 live entries (total: 44)
[utils.ml] union_find_classes:
  14 live entries (total: 14)
Goodbye!
	0:21.75 real,	31.50 user,	1.88 sys,	0 amem,	667 248 mmem
```
