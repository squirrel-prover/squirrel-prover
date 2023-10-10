abstract i : index.

abstract f : (index -> index) -> index.
abstract g : index -> (index -> index).
print f.
print g.

abstract a : index -> index * index -> index.
print a.
op foo = a i (i,i).

abstract b : (index -> index) * (index -> index).
print b.
op bar0 = (b#1) i.
op bar1 = (b#2) i.

abstract r : (index -> index) * index -> index.
print r.
op foor (x : (index -> index) * index) : index = r x.

abstract c : (index * index) * index.
print c.

op c1 = (c#1)#1.
op c2 = (c#1)#2.
op c3 = c#2.

abstract d : index * (index * index).
print d.
op d1 = (d#2)#1.
op d2 = (d#2)#2.
op d3 = d#1.
