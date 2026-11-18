"""Finite checks of chamber topology, exact terminal cut costs and Boolean penalties."""
from collections import Counter, defaultdict, deque
from itertools import combinations, product
from math import inf


class Mesh:
    def __init__(self):
        self.parent = []
        self.faces = []

    def new(self, n):
        first = len(self.parent)
        self.parent.extend(range(first, first + n))
        return tuple(range(first, first + n))

    def root(self, v):
        while self.parent[v] != v:
            self.parent[v] = self.parent[self.parent[v]]
            v = self.parent[v]
        return v

    def glue(self, outer, boundary):
        for a, b in zip(outer, reversed(boundary)):
            self.parent[self.root(a)] = self.root(b)

    def puncture(self, outer):
        inner = self.new(3)
        for i in range(3):
            j = (i + 1) % 3
            self.faces.extend([(outer[i],outer[j],inner[j]),(outer[i],inner[j],inner[i])])
        return inner

    def punctured_sphere(self, n):
        top, bottom = self.new(2)
        ring = self.new(n)
        hats = []
        for i in range(n):
            j = (i+1) % n
            hats.append(self.puncture((top,ring[i],ring[j])))
            self.faces.append((bottom,ring[j],ring[i]))
        return hats

    def chamber(self, d):
        outer, terminals, arms = [], [], []
        for _ in range(d):
            disk = self.new(3)
            center, = self.new(1)
            outer.append(disk)
            for i in range(3):
                a, b = disk[i], disk[(i+1)%3]
                mid, = self.new(1)
                terminals.append(len(self.faces))
                self.faces.append((a,b,mid))
                arms.append([self.puncture((b,center,mid)),self.puncture((center,a,mid))])
        count = len(terminals)
        for arm in range(2):
            ports = {}
            for i in range(count):
                hats = self.punctured_sphere(count)
                self.glue(arms[i][arm],hats.pop())
                for j in range(count):
                    if i != j:
                        ports[i,j] = hats.pop()
            for i,j in combinations(range(count),2):
                self.glue(ports[i,j],ports[j,i])
        return outer, terminals

    def audit(self, closed):
        faces = [tuple(map(self.root, face)) for face in self.faces]
        assert len(set(map(frozenset,faces))) == len(faces)
        edges, links = defaultdict(list), defaultdict(lambda: defaultdict(list))
        for i,(a,b,c) in enumerate(faces):
            assert len({a,b,c})==3
            for v,x,y in [(a,b,c),(b,c,a),(c,a,b)]:
                edges[tuple(sorted((x,y)))].append((i,x<y))
                links[v][x].append(y)
                links[v][y].append(x)
        for adj in links.values():
            frontier = [next(iter(adj))]
            seen = set(frontier)
            for x in frontier:
                for y in adj[x]:
                    if y not in seen:
                        frontier.append(y)
                        seen.add(y)
            assert len(seen)==len(adj)
            deg = Counter(map(len,adj.values()))
            assert set(deg) <= {1,2} and deg[1] in ({0} if closed else {0,2})
        dual=[]
        for a in edges.values():
            if len(a)==1:
                assert not closed
            else:
                assert len(a)==2 and a[0][1]!=a[1][1]
                dual.append((a[0][0],a[1][0]))
        return dual


def cut(edges, terminals, bits):
    graph=defaultdict(Counter)
    for a,b in edges:
        graph[a][b]+=1
        graph[b][a]+=1
    for t,bit in zip(terminals,bits):
        a,b=(-1,t) if bit else (t,-2)
        graph[a][b]=len(edges)+1
    total=0
    while True:
        prev={-1:None}
        q=deque([-1])
        while q and -2 not in prev:
            a=q.popleft()
            for b,v in graph[a].items():
                if v>0 and b not in prev:
                    q.append(b)
                    prev[b]=a
        if -2 not in prev:
            return total
        b=-2
        while b!=-1:
            a=prev[b]
            graph[a][b]-=1
            graph[b][a]+=1
            b=a
        total+=1


def main():
    tests=0
    for d in (1,2):
        mesh=Mesh()
        rings,ts=mesh.chamber(d)
        dual=mesh.audit(False)
        for bits in product((0,1),repeat=len(ts)):
            t=min(sum(bits),len(ts)-sum(bits))
            assert cut(dual,ts,bits)>=2*t
            tests+=1
        other,_=mesh.chamber(d)
        for a,b in zip(rings,other):
            mesh.glue(a,b)
        mesh.audit(True)
    for a,b,h in product((0,1),repeat=3):
        penalty=a*b-2*a*h-2*b*h+3*h
        assert (penalty==0)==(h==(a&b)) and penalty>=0
    graphs=0
    pairs=list(combinations(range(5),2))
    for mask in range(1<<len(pairs)):
        edges=[e for i,e in enumerate(pairs) if mask>>i&1]
        for bits in product((0,1),repeat=5):
            costs=sum(bits[u]+bits[v]+(bits[u]==bits[v]) for u,v in edges)
            assert (costs==len(edges))==all(not(bits[u] and bits[v]) for u,v in edges)
        graphs+=1
    print(tests,"terminal cut tests; two closed simplicial gluing tests;",graphs,"independent-set gadgets; all passed")


if __name__=="__main__":
    main()
