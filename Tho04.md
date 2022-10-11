# Compact Oracles for Reachability and Approximate Distances in Planar Digraphs

## Introduction
Let $G=(V,E)$ be a planar digraph with $n$ vertices. We can preprocess this graph in $O(n \log{n})$ space and time to produce an oracle that answers reachability queries (ie. whether vertex $u$ is reachable from vertex $v$) in constant time.

A stretch-$t$ distance oracle provides distances that are at most $t$-times larger than the true shortest-path distance in $G$.

This reachability oracle distributes into labeling schemes: each vertex gets an assigned label $l(.)$ such that given $l(v), l(w)$, we can compute if $v$ reaches $w$ in constant time. In approximate oracles, we get labels of size $O(\log{nN} \log{n}/\epsilon)$ so that we can compute distances with $(1+\epsilon)$-stretch in $O(\log{\log{nN}}+1/\epsilon)$ time. For undirected graphs, this becomes $O(\log{n}/\epsilon)$ calculation time and $O(1/\epsilon)$ query time.

New technique used in this paper is a dipath decomposition. This associates a small set $S(v)$ of dipaths with each vertex $v$ such that any dipath from vertex $u$ to $w$ will be in the set $S(u) \cap S(w)$. Each $S(v)$ is logarithmic in size. For each $Q \in S(v)$, we can store the number $to_v[Q]$, defined as the first vertex in Q reachable by $v$, and $from_v[Q]$, the last vertex in Q reachable by $v$. Then we can reach $u$ from $w$ iff there is a $Q \in S(u) \cap S(w)$ such that $to_u[Q] \leq from_w[Q]$. 

## Reachability oracle
We will construct a series of 2-layered digraphs $G_0,...,G_k$ so that any reachability question in G can be addressed to a constant number of such digraphs so each digraph admits separators (a set of dipaths is a separator if removing all these vertices in these dipaths splits the graph into components that are at most half the size of original graph) that consists a constant number of dipaths. 

### 2-Layered Digraphs
We reduce reachability in G into reachability in some digraphs with special properties, which preserves planarity of $G$.

**t-layered spanning tree.** A tree T in a digraph $H$ that is a disoriented (removing all directions), rooted spanning tree such that a path in T from its root concatenates at most $t$ dipaths in $H$. We say $H$ is $t$-layered if such a spanning tree exists.

*Lemma 2.2* Given a digraph $G$, we can construct a series of digraphs $G_0,...,G_{k-1}$ in linear time such that:
1. The total number of edges and vertices in all $G_i$ is linear in the number of edges and vertices in $G$.
2. Each vertex $v$ has index $i(v)$ such that $w$ is reachable from $v \in G$ iff it is reachable from $v \in G_{i(v)-1}$ or $G_{i(v)}$.
3. Each $G_i$ is a 2-layered digraph with 2-layered spanning tree $T_i$ with root $r_i$
4. $G_i$ is a minor of $G$: it is obtained from $G$ by deletion of edges and vertices and contractions of edges. $G_i$ will be planar is $G$ is.
*Proof.* Assume $G$ is connected in the undirected sense, otherwise apply the argument to each connected component independently. We partition $V(G)$ into layers $L_0,...,L_{k-1}$ where $L_0$ is the set of vertices reachable from a vertex $v_0$ and thereafter alternates between vertices reaching or reachable from previous layers. A layer contains all vertices reaching or reachable from previous layers. If $i$ is odd, $L_i$ is all the vertices where $v$ reaches $L_0,...,L_{i-1}$. If $i$ is even, $L_i$ is all the vertices reachable by $L_0,...,L_{i-1}$.

Each digraph $G_i$ consists of two consecutive layers with all preceding layers contracted to a single vertex. For $G_0$ we set $r_0=v_0$, and we set all the contracted layers' vertex into $r_i$.

By construction, $G_i$ must satisfy 4., and since the layering partitions a vertex such that each vertex can appear as a non-root node at most twice, 1. is satisfied since we have at most $2n+k=O(n)$ vertices, and at most $2n$ edges incident to the roots with each edge occurring at most twice, giving $2n+2m=O(m)$ edges.

Consider a dipath $P$ from $v$ to $w$. Let $i$ be the lowest index of layer intersected by $P$ and let $x$ be a vertex in the intersection. By definition, if $j \geq i$ is even then $L_{\leq i}$ constains the part of path $P$ after vertex $x$ (all vertices reachable by a vertex in previous layer). If $j \geq i$ is odd, then $L_{\leq i}$ contains the part of $P$ before $x$ (all vertices that reach the layers before it).
