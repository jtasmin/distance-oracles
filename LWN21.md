# Preliminaries
Let $G = (V,E)$ be a graph and $w$ be the weight function on E(G). Let $SP(x,y)$ be the shortest-path and $d_G(x,y)$ be this shortest-path distance between $x,y \in V(G)$. Define the *spread* of G, $\Delta = \frac{max_{u,v}d_G(u,v)}{min_{u \neq v}d_G(u,v)}$ as the max-to-min ratio of shortest-path distances.

For a tree T, let $T[x,y]$ be the unique path between $x,y \in V(T)$. For a closed curve $C \in \mathbb{R^2}$, removing it divides the plane into interior and exterior denoted *Int(C)* and *Ext(C)*.

Let $G$ be a graph with planar embedding, and $G_\Delta$ be a triangulation of $G$. *Pseudo-edges* are defined as $E(G_\Delta)-E(G)$. If T is a shortest-path tree of G (ie. contains the shortest path between any two vertices in T), then T is a spanning tree of $G_\Delta$. 

A fundamental cycle of $G$ is formed by adding one edge to a spanning tree $T$ of $G$ such that there are two paths between any vertices of $G$ on this cycle. The *shortest path separator C* of G is a fundamental cycle of $G_\Delta$ with respect to a spanning tree $T$. Since there are edges in $G_\Delta$ that are not in $G$, $C$ consists of two paths of $G$ rooted at the same end vertex and another edge between the two other endpoints of these paths (which may be a pseudo-edge). We call this a shortest-path separator because they split up the graph 

**Planar separator theorem (Lemma 2).** Let $T$ be a shortest path tree rooted at some vertex $r$ of an edge-weighted planar graph $G$, let $\omega : V \rightarrow \mathbb{R^+}$ be a weight function on $V(G)$ with $W=\sum_{u\in V(G)} \omega(u)$. Then there is a shortest path separator $C$ of $G$ such that max$\omega(V(G) \cap \text{Int(C)})$, with $\omega(V(G) \cap \text{Ext(C)})) \leq \frac{2W}{3}$. In other words, there is a small number of vertices that we can remove from $G$ to split this planar graph into disjoint subgraphs, each of which has at most $W$ weight in total.

**r-divisions.** Let $r \geq 1$ be an integer and $G$ be a planar graph with $n$ vertices. An $r$-division of $G$ partitions $E(G)$ into subsets that induce subgraphs of $G$ called *pieces* $\{R_1,...,R_k\}$ such that:
- $k=O(\frac{n}{r})$ and $|V(R_i)| \leq r, \forall i \in [1,k]$
- $|\delta R_i| = O(\sqrt{r})$, where $\delta R_i$ refers to the boundary vertices (each boundary vertex has at least one neighbour outside $R_i$).
An r-division can be computed in linear time (KMS13).

**Approximate labeling schemes (Thorup, Klein).** Similar constructions of a $(1+\epsilon)$-approximate distance oracles for edge-weighted undirected planar graphs of $n$ vertices with $O(n \log{n \epsilon^{-1}})$ space, $O(\epsilon^{-1})$ query time, with oracle construction in nearly linear time. The distance oracle here can be distributed as a *labeling scheme* where each vertex is assigned a label of $O(\epsilon^{-1} \log{n})$ words with a decoding function that returns a $(1+\epsilon)$-approximate distance between $u,v$ by only looking at their labels.

**Sparse cover.** A $(\beta,s,\Delta)$-sparse cover of a graph $G=(V,E)$ is a collection of clusters (subgraphs) of $G$ denoted $\mathbf{C}=\{C_1,...,C_k\}$ such that we get a cover for the edges of $G$ that has a bounded diameter with small degree (max. number of clusters that each vertex is part of).
1. Diameter (max of diameters (distance between nodes) for all vertices) of $C_i \leq \Delta$ for any $i \in [1,k]$
2. $\forall v \in G, B_G(v,\Delta/\beta) \subseteq C_i$ for some $i \in [1,k]$, i.e. `` what is $B_G$?
3. Each $v \in V$ is in at most $s$ clusters.

*Theorem 7.* Edge-weighted planar graphs admit a (O(1),O(1))-sparse covering scheme. Lemma 1 constructs a sparse cover in linear time given diameter.

**Weak nets.** Given an edge-weighted graph $G$ with terminal nodes $K \subseteq V$, a weak $(r,\gamma)$-net of $K$ for $\gamma \geq 1$ is a subset of vertices in $K$ such that:
1. $d_G(p,q) \geq r$ for $p \neq q \in N$
2. for each $x \in K$ there exists a $p \in N$ such that $d_G(p,x) \leq \gamma r$ (there is a close-by vertex in $N$ for each vertex in $K$)

An assignment $\mathcal{A}$ associated with a weak net $N$ is a family of subsets of $K$ such that for each $x \in N$ there exists a set $\mathcal{A}[x] \subseteq K$ that contains $x$ and $d_G(x,y) \leq \gamma r$ for each $y \in \mathcal{A}[x]$. An assignment $\mathcal{A}$ covers K if $\bigcup_{A \in \mathcal{A}} = K$.

**Lowest common ancestor (LCA).** Given a tree $T$, an LCA data structure returns the lowest common ancestor of two vertices $u,v \in T$ and this data structure can be constructed in linear time with $O(|V(T)|)$ space, $O(1)$ query time.
