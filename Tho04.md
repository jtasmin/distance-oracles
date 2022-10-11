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

Observe that 2. is satisfied. Consider a dipath $P$ from $v$ to $w$. Let $i$ be the lowest index of layer intersected by $P$ and let $x$ be a vertex in the intersection. By definition, if $j \geq i$ is even then $L_{\leq i}$ constains the part of path $P$ after vertex $x$ (all vertices reachable by a vertex in previous layer). If $j \geq i$ is odd, then $L_{\leq i}$ contains the part of $P$ before $x$ (all vertices that reach the layers before it). So $P$ is contained in $L_i \cup L_{i+1}$, so $P$ is in $G_i$. Since we know $v \in P$ is contained in $G_{i(v)-1}$ and $G_{i(v)}$ so $P$ from $v$ to $w$ must be in one of those two digraphs.

Construct the undirected spanning trees $T_i$ and suppose $i$ odd. By definition then $r_i$ reaches all of $L_i$ so a spanning tree $U_i$ of $\{r_i\} \cup L_i$ can be constructed with edges oriented away from $r_i$. $\{r_i\} \cup L_i$ is reached by $L_{i+1}$ so we can extend $U_i$ into a spanning tree of $\{r_i} \cup L_i \cup L_{i+1} = V(G_i)$ but with edges oriented towards $\{r_i\} \cup L_i$. Any path in $T_i$ from $r_i$ now has a first part oriented from $r_i$ and second part oriented towards $r_i$ so 3. is satisfied. The case where $i$ even is similar, but flipping the part orientations.

Applying Lemma 2.2 to a planar digraph for reachability, then we can assume we are dealing with a 2-layered planar digraph. We make reachability oracles for each $G_i$ and address reachability queries from $v$ in $G$ to $G_{i(v)-1}$ and $G_{i(v)}$.

### Undirected Planar Spanning Tree Separation
We take a planar digraph $H$ ith a 2-layered spanning tree $T$ without edge orientations, viewing it as an undirected graph with given rooted spanning tree $T$. We will find three root paths in $T$ whose removal separates $H$ into components at most half its size using planarity. Each of these paths correspond to at most six dipaths in the original digraph.

*Lemma 2.3.* Given an undirected planar graph $H$ with rooted spanning tree T and non-negative vertex weights, we can find vertices $u, v, w$ such that each component of $H - V(T(u) \cup T(v) \cup T(w))$ contains at most half the weight of $H$.
*Proof.* By Lipton, Tarjan [1979] but instead we use 1/2 the weight and not 2/3 the weight in each component. First we embed the graph on a sphere and triangulate $H$ by adding edges. Then $T$ is a spanning tree also for $H^{\triangleleft}$ with any separator of $H^{\triangleleft}$ is also a separator of $H$.

Consider a triangle $\Delta$ of $H^{\triangleleft}$, viewing $\Delta$ as the external face. A fundamental cycle of an edge in $T$ is the cycle consisting of the edge and the unique path between its endpoints in $T$, and the *inside* of this cycle is the side that does not contain $\Delta$. If $(v,w) \in T$ then the inside is empty. If $u,v,w$ are corners of $\Delta$ then each component of $H^{\triangleleft} - V(T(u) \cup T(v) \cup T(w))$ is contained in the fundamental cycle of one of the boundary edges (that is, $(u,v), (v,w), (w,u)$). We want to identify $\Delta$ as an external face so none of the fundamental cycles of the boundary edges of $\Delta$ have more than half its weight strictly inside (excluding vertex weights on the fundamental cycle).

Let $\Delta$ be an arbitrary triangle. If the fundamental cycle of one of the boundary edges - say $(u,v)$ - has more than half the weight strictly inside we consider $\Delta'$ on the other side of $(u,v)$. Keep doing this, observing that it terminates because turning the cycle 'inside out' means that the new triangle $\Delta'$ has at most half the weight. If, however, the third corner of $\Delta'$ is $w'$ then the new insides of the fundamental cycles of $(u,w'), (v,w')$ are both contained in the previous 'inside face' of $(u,v)$ without $\Delta'$. So both have fewer triangles than previous inside of $(u,v)$.

<img width="492" alt="Screenshot 2022-10-11 at 14 15 05" src="https://user-images.githubusercontent.com/69584282/195168431-4aee8f08-359c-4634-9d79-7da897793867.png">

In Lipton, Tarjan [1979] the above construction can be implemented in linear time. First we embed, triangulate the graph and pick arbitrary triangle and find the weight inside the fundamental cycle of the boundary edges. Then we have a loop, moving $\Delta$ to neighboring triangle. Each time we find the weight of the new inside face of the fundamental cycle of each boundary edge.

### Reachability via a Dipath

