"""Finite controls for exact label permutations in the subspace encoding."""
from itertools import permutations, product

FIELD = 3

def vectors(size):
    return list(product(range(FIELD), repeat=size))

def apply(matrix, vector):
    return tuple(sum(a*b for a,b in zip(row,vector)) % FIELD for row in matrix)

def invertible_matrices(size):
    points = vectors(size)
    for matrix in product(points, repeat=size):
        if len({apply(matrix, x) for x in points}) == len(points):
            yield matrix

def multiply(a, b):
    return tuple(tuple(sum(x*y for x,y in zip(row,col)) % FIELD
                       for col in zip(*b)) for row in a)

def negate(a):
    return tuple(tuple(-v % FIELD for v in row) for row in a)

def graphs(matrix, dimension, input_map, output_map):
    return sorted((frozenset((apply(input_map,x), apply(output_map,apply(sign_matrix,x)))
                            for x in vectors(dimension))
                  for sign_matrix in (matrix,negate(matrix))), key=lambda s: sorted(s))

def controls(source, target, dimensions):
    xdim, ydim = dimensions
    def identity(d):
        return tuple(tuple(int(i==j) for j in range(d)) for i in range(d))
    count = 0
    for p,q,pi in product(invertible_matrices(xdim),invertible_matrices(ydim),
                          permutations(range(len(source)))):
        raw = all(multiply(q,a) in (multiply(target[j],p),negate(multiply(target[j],p)))
                  for a,j in zip(source,pi))
        reflected = all(graphs(a,xdim,p,q)==graphs(target[j],xdim,identity(xdim),identity(ydim))
                        for a,j in zip(source,pi))
        assert raw == reflected
        count += 1
    return count

print("Transporter controls:", sum([
    controls([((1,0),(0,1)),((0,0),(0,0)),((1,1),(0,0))],
             [((0,0),(0,0)),((2,0),(0,2)),((2,2),(0,0))], (2,2)),
    controls([((1,0),),((1,0),),((0,1),)],[((0,1),),((1,0),),((1,0),)],(2,1)),
    controls([((0,),),((1,),)],[((1,),),((1,),)],(1,1)),
]))
