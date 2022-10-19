# Compact Oracles for Reachability and Approximate Distances in Planar Digraphs

## Introduction
Let $G=(V,E)$ be a planar digraph with $n$ vertices. We can preprocess this graph in $O(n \log{n})$ space and time to produce an oracle that answers reachability queries (ie. whether vertex $u$ is reachable from vertex $v$) in constant time.

A stretch-*t* distance oracle provides distances that are at most $t$-times larger than the true shortest-path distance in $G$.

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

*Proof.* Assume $G$ is connected in the undirected sense, otherwise apply the argument to each connected component independently. Partition $V(G)$ into layers $L_0,...,L_{k-1}$, where $L_0$ is the set of vertices reachable from a vertex $v_0$ and thereafter alternates between vertices reaching or reachable from previous layers. A layer contains all vertices reaching or reachable from previous layers. If $i$ is odd, $L_i$ is all the vertices where $v$ reaches $L_0,...,L_{i-1}$. If $i$ is even, $L_i$ is all the vertices $v$ reachable by $L_0,...,L_{i-1}$.

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

<img width="514" alt="Screenshot 2022-10-11 at 14 20 02" src="https://user-images.githubusercontent.com/69584282/195169345-dbac7dbf-bc42-4c86-9798-46f6e652286c.png">

In Lipton, Tarjan [1979] the above construction can be implemented in linear time. First we embed, triangulate the graph and pick arbitrary triangle and find the weight inside the fundamental cycle of the boundary edges. Then we have a loop, moving $\Delta$ to neighboring triangle. Each time we find the weight of the new inside face of the fundamental cycle of each boundary edge.

### Reachability via a Dipath
Now we showe that we can use separator dipaths to represent directed reachability efficiently. A vertex $u$ reaches $w$ via dipath $Q$ if there is a dipath from $u$ to $w$ intersecting $Q$.

There is a dipath from $u$ to $w$ intersecting $Q$ iff $u$ connects to $a$ in $Q$ and $w$ connects from $b$ in $Q$ where $a$ equals or precedes $b$ in $Q$. (Assuming numbered vertices in $Q$ for checking precedence in constant time. 

<img width="492" alt="Screenshot 2022-10-11 at 14 15 05" src="https://user-images.githubusercontent.com/69584282/195168431-4aee8f08-359c-4634-9d79-7da897793867.png">

*Lemma 2.5.* For any digraph $H$ and dipath $Q$ we identify all connections between vertices in $H$ and dipath $Q$ in linear time.

*Proof.* We use recursion to identify connections from $Q$, which is all we need because we can use symmetry for connections from $H$. 
1. Use a BFS to find all vertices $v$ reached by the last vertex in $Q$, $t$. 
2. Now remove all reached vertices (including $t$) from $H$ and $Q$
3. Recur on the remaining vertices. Observe that each edge is considered once so this is linear. 

Observe that if $t$ reaches a vertex $x \in Q$, $t$ reaches all the successors of $x \in Q$ so it is a 'suffix' (ending part) of $Q$ that we remove. So $Q$ remains a dipath. If $P$ was a dipath from a vertex in $Q$ to a vertex $v$ and a vertex from $P$ is removed then observe that $t$ must reach $v$ (by the recursion steps above). So no connections except those from $t$ are destroyed.

### Algorithm for $O(\log{n})$-query time Reachability Oracle
Let $G$ be a planar digraph. By Lemma 2.2 we reduce our problem to 2-layered digraphs. Consider a 2-layered digraph $H$ with a 2-layered rooted spanning tree $T$. Apply Lemma 2.3 to produce a separator $S$ with three root paths corresponding to six separator dipaths in $H$. With unit vertex weights we know each component of $C$ of $H-V(S)$ has at most half the weight of $H$.

For each dipath $Q \in S$ we apply Lemma 2.5 to produce all connections between $H,Q$. For each vertex $v$ we make two arrays: $to_v, from_v$, indexed by the separator dipath, where $to_v[Q]$ is the number of the vertex that $v$ connects to in $Q$ and $from_v[Q]$ is the number of the vertex that $v$ connects from. If $v$ does not reach $Q$ then $to_v[Q] = \infty$ and if $Q$ does not reach $v$ then $from_v[Q] = -1$. Then $u$ reaches $w$ via the separator $S$ iff $to_v[Q] \leq from_v[Q]$ for some dipath $Q \in S$. This takes constant time to check for given $Q$.

S is a connected part of the spanning tree $T$ including the root because it consists of root paths. Then contract $S$ into root vertex $r^S$, giving us a resulting 2-layered digraph $H/S$ with spanning tree $T/S$ rooted at $r^S$. We give $r^S$ zero weight because we are not interested in connections via $r^S$. For each component of $H-V(S)$ we recur on the subgraph $H' := C \cup \{r^S\}$. Because we give $r^S$ zero weight then total weight in $H' \leq 1/2$ total weight in $H$.

Using Lemma 2.3 (finding vertices such that each component of $H-V(T(u) \cup T(v) \cup T(w))$ has at most half weight of $H$) we find a separator $S'$ of $H'$, but we remove $r^S$ from $S', H'$ since it is suppressed when finding connections between vertices in $H'$ and dipaths in $S'$. At the next level of recursion we have components $C'$ of the graph $H-V(S')$ which are at most half the weight of $C$, so we get $O(\log{n})$ recursion calls with total runtime of $O(n \log{n})$.

### Indexing the Separator Dipaths
Each vertex $v$ takes parts in calls on a path in the recusion tree that goes from the root to where $v$ is selected for a separator $S$, which we call the *final call* of $v$. These numbers, used as indices for $to_v, from_v$ are $O(\log{n})$, which is also the size of these to and from tables for each vertex.

Let the dipaths in each separator of each call have a fixed ordering, which the enumeration by vertices participating in the call respects. Let $Q$ be a separator dipath in a call with $u$ and $w$, then $u$ and $w$ will use the same index for $Q$. To check reachability from $u \rightarrow w$ we only need to consider calls involving both vertices. **If the number of separator dipaths in calls like these are $s$, then $u$ reaches $w$ iff for some $q \in \{ 1,...,s \}$, $to_u[q] \leq from_w[q]$.** This check take $O(\log{n})$ time since $s = O(\log{n})$.

To find $s$ we store a separation number with each call $C$. The separation number is the number of separator dipaths in ancestor calls of (and including) $C$. So $s$ is the separation number of the nearest common ancestor call of the finall calls of $u, w$. Finding this nearest common ancestor is $O(\log{n})$ because our recursion tree is logarithmic in depth, so this is our overall query time for reachability.

### Reducing Query Time to $O(1)$
To achieve constant-time querying, we will pass down a set of root paths $F$ called the frame of $H$, that separate the subgraph $H$ from the rest of $G_i$. (This means $H$ will be a component of $G_i - V(F)$. Let $S$ be a separator of $H$ that separates $u,w$. Then $F \cup S$ separates $u,w$ in $G_i$. 

For each dipath $Q \in F \cup S$ we will identify the connections between $H,Q$ over $G_i$, such that $v \in V(H)$ connects to the first vertex in Q, and connects from the last vertex in Q that $v$ can reach in $G_i$. Since $F,S$ are constant in size we only have a constant number of separator and frame dipaths to query so we can check reachability from $u, w$.

The union of elements of $F$ is a tree of the same root as our rooted spanning tree. Since we want to minimise the number of root paths in $F$ we assume that these are root paths from leaves to tree, since additional root paths would not affect V(F) they are redundant. So we also call the root paths in $F$ the leaves of $F$.

### Few-frame Paths
We alternate between subgraph recursion (each of the new subgraphs have few vertices) and frame-reducing recursion (each new subgraph gets a frame with few leaves) to keep the frames constant in size.

Let $H+F$ be all of $H,F$ together with all the edges from $G_i$ between $H$ and $F$. Pick the separator $S =\{T(u) \cup T(v) \cup T(w)\}$ so that no component of $(H+F)-V(S)$ contains more than half the vertices in $H$. Applying Lemma 2.3, we know that we can find this by putting vertices in $H$ with weight 1, vertices in $F$ with weight 0.

In frame-reducing recursion we pick $S$ so no component of $(H+F)-V(S)$ contains more than half the leaves of $F$. Applying Lemma 2,3 in this case gives leaves with weight 1 and all other vertices get weight 0. Each of these recursion steps halves the weight of subgraph $H$ so we still only have logarithmic recursion steps.

We want to know how many root paths are in the frames passed down in recursion steps on the components of $H-V(S)$. Start with a subgraph reducing recursion: let original frame $F$ have $f$ root paths, then reach component receives a frame with at most $f+3$ root paths (those in $F$ and the three from $S$, the separator). For a frame-reducing recursion, we always pass down $S$ as a frame but can avoid passing down some of $F$'s root paths. Let $R \in F$ be a root path with leaf node $x$: when $R$ as a path intersects the separator $S$ then the rest of $R$ is contained in $S$. If $x \in S$ we do not need to include it as a separate root path, and only components of $H-V(S)$ with $x$ that need $R$ in their frame. Let $f'$ be the number of root paths currently in $F$. By our choice of $S$ (and Lemma 2.3), no component of $H-V(S)$ contains more than $f'/2$ leaves from F, and including the three root paths from $S$, we pass down at most $f'/2 +3$ root paths down in recursion.

The frame is empty in the root call on $G_i$. Generally, we go from $f \rightarrow$ at most $f+3$ to $(f+3)/2 +3 = f/2 + 4.5$ for one subgraph and one frame-reducing recursion. So the maximal number of frame paths for a subgraph reducing recursion if $f \leq 9$ and it is $f' \leq f+3 \leq 12$ for a frame-reducing recursion. These paths correspond to at most 2 dipaths in the frame.

### Reachability via Framed Separators
We need all connections over $G_i$ between $H$ and dipaths in frame $F$ and separator $S$ to answer reachability queries in $G_i$. Assume that all of the connections in $G_i$ between $H$ and the dipaths in the frame are passed down in recursive steps. Let $H \star F$ denote $H+F$ and the connections as edges. Let $u,w \in V(H)$, then $u$ reaches $w$ if and only if it does so in $H \star F$ (which is typically nonplanar, and these extra edges is linear in $n$ since each $v \in V(H)$ has one connection to and from the connection of each of the constant number of dipaths in $F$).

We aim to reduce $H \star F$ in size to something linear in number of edges of $G_i$ that are incident to vertices in $H$. We call a vertex in $F$ topological if it is an endpoint of a dipath in $F$ or a branching point between dipaths in $F$ (there are a constant number of these vertices). Let $v \in V(F)$ selected by H if it neighbours a vertex of $H$ in $H \star F$. Skipping vertices that are not topological or selected, if we have a segment of a dipath whose interior vertices are neither of the above then we contract it to a single edge. With this reduced $F$, we apply Lemma 2.5 (linear-time connection finding between digraph and dipath) to $H \star F$ and find all connections in $G_i$ between vertices in $H$ and dipaths in $S$.

To construct the reduced frame efficiently we do it as we recur, skipping vertices that are neither topological nor selected. So for each component $H'$ or $H-V(S)$ we first need to construct the reduced frame $F'$ in two phases.
1. For each component $H'$ we take the dipaths and vertices from $F$ and $S$ needed for $F'$. Record these dipaths and vertices that are relevant to $H'$. 
2. Traversing Q, when we arrive at some vertex we consider the components $H'$ that it's relevant for. Each component $H'$ has registered its last relevant vertex $u$ from Q so we can add $(u,v)$ to its reduced representation $Q'$
Overall processing time is still linear in the size of $H \star F$ so overall runtime is $O(n \log{n})$.

### Indexing with Frames
When enumerating dipaths from a vertex $v$, we want to enumerate both the dipaths in the frame and those in the separator in each ancestor call of the final call of $v$. In this case, the same dipath often gets numbered several time first as a separator and later as a frame. Let the separation number of a call be the last number used for enumerating dipaths for that call. Let $C$ be the nearest common ancestor of the final calls of $u,w$, and $s$ be the separation number of $C$. Let $p$ be the separation number of the parent of $C$ such that $\{p+1,...,s\}$ are the indices of this frame and the separator dipaths of $C$ so $u$ reaches $w$ in $G_i$ iff there exists a $q \in \{p+1,...,s\}$ such that $to_u[q] \leq from_w [q]$.

If we apply the linear-time preprocessing algorithm by Harel and Tarjan [1984] to the recursion tree, we can get the nearest common ancestor call $C$ in constant time, which also gives us the separation numbers $s,p$ of $C$ and its parents. From this, then we conclude:

**Theorem 2.6.** We can preprocess a planar digraph in $O(n \log{n})$ time and space to produce an $O(n \log{n})$-space reachability oracle that can determine if $u$ reaches $v$ in constant time.

## A Pure Label-Based Implementation
Now we show that the reachability oracle can be distributed as a labeling scheme by associating each vertex $v$ with a label $l(v)$ of size $O(\log{n})$ so that only when given $l(u), l(w)$ we can detemine if u reaches w.

We have $O(\log{n})$-space tables $from_v$ and $to_v$. The separation numbers are stored globally with calls in the recursion tree but instead for each vertex $v$ and depth $d$ we store the separation number $s_v[d]$ of the depth d ancestor of the final call of $v$ in the recursion tree. So all we have to do is now find a labeling for depths of nearest common ancestors. To get constant query time, we translate Harel, Tarjan's technique into a labeling scheme: observe that whenever global information is accessed it is associated with an ancestor tree of $O(\log{n})$ height, and if we copy this information down to each descendant we get the desired label of $O(\log{n})$ space. This increases our nearest-common ancestors space to $O(n \log{n})$ which is equal to the global space.

**Theorem 2.7.** The oracle of Theorem 2.6 can be distributed as a labeling scheme with labels of size $O(\log{n})$.

### Finding Dipaths
If we find that $u$ reaches $w$, next we want to produce a dipath from $u$ to $w$ in time linear to path length.
#### Pathfinding in the Basic Recursion
If $u$ reaches $w$ then our query algorithm finds an index $q$ of a separator dipath $Q$ of a digraph $H$ such that:
1. the connection via $H$ from $u$ to $Q$ precedes the connection via $H$ from $Q$ to $w$
2. all dipaths from $u$ to $w$ in $H$ are also dipaths in the original digraph $G$.

Extending Lemma 2.5, we provide dipaths that witness the connections between $H$ and $Q$. In Lemma 2.5, the proof finds a forest of disjoint $from$-trees oriented away from roots in $Q$ such that $a$ is the root of $v$ if and only if $(a,v)$ is the connection from $Q$ to $v$. Symmetrically, we can witness connections from $H$ to $Q$ and get a forest of $to$-trees oriented towards roots in $Q$.

We save the parent pointers of the $to$ and $from$ trees using $q$ as an index. We let $to_v[q]$ store the parent of the $v$ in the to-trees generated from $Q$, and if $v$ is a root then this is nil and if $v$ does not reach $Q$ then it is undefined. Similarly, $from_v[q]$ stores the parent of $v$ in the from-trees generated from $Q$. These parent pointers don't affect our asymptotic space bounds.

Given the index $q$, with $to_u[q] \leq from_w[q]$ we follow parent points by tracing a dipath from $u$ to $a \in Q$ and follow the parent pointers $from_v[q]$ tracing backwards to get a dipath from $b \in Q$ to $w$ where $b$ equals or succeeds $a \in Q$. If $Q_0$ is a segment of $Q$ from $a$ to $b$ then $P_1Q_0P_2$ is a dipath from $u$ to $w$ that we find in linear time in its length.

We ensure that the dipath can be generated without loops [fill in this section].

### Pathfinding with Constant Query Time
Witnessing dipaths combined with the constant query time from Section 2.5. The problem is not all dipaths from $u$ to $w$ in $H$ are also dipaths in the original digraph $G$. More precisely, if $u$ reaches $w$, our query algorithm returns an index $q$ of a separator dipath $Q$ of a digraph $H \star F$ from $Q$ to $w$. This means we can find a dipath $P$ in $H \star F$ from $u$ to $v$ via $Q$. However, $H \star F, P$ may contain edges that are not edges in the original digraph. 

The idea is when we recur on $H$ with frame $F$ and separator $S$, besides making global connections over $H \star F$ between $Q \in F \cup S$ and $H$, we make local connections over $H$ between dipaths $Q \in S$ and $H$. These local connections can be turned into dipaths via parent pointers. So if $u$ reaches $w$ in $G_i$, our goal is to compute $sep(u,w)$ denoting an index of a separator dipath $Q$ of an ascending (from a call ascending from the final calls of u,w) digraph $H$ such that there exists a dipath from $u$ to $w$ in $H$ which intersects $Q$. The indexing of separator dipaths for these local connections is exactly the same as the basic recursion, and we compute the separation index based on information stored within the global connections found by our reachability query.

In our recursion we are going to label all edges and global connections with their $sep$-values. When recurring with $H\star F$ we assume that we have labels for all edges $(x,y)$ that are not in H. When we pick a separator $S$ we index the separator dipaths in some order (the one described in 2.4). Then going through the dipaths in this order, and taking all edges incident to (and including) those in $Q$ that have not been labeled and we label them with the index of $Q$. Now we construct the global connections over $H \star F$ between $Q$ and $H$, and these global connections are witnessed by $to$ and $from$ trees in $H \star F$. A global connection $(v,a),a \in Q$ is now labeled with the smallest label on the path from v to its root $a$ in the to-trees. Similarly, $(b,v), b\in Q$ is labeled with the smallest label on the path from $v$ to its root $b$ in the from-trees. Processing the $to$ and $from$ trees top down, we can label the global connections in time linear to the sizes of the trees, resulting in $O(n \log{n})$ total time.

To see that the above labeling of the global connections with the $sep$-values will be correct, consider a dipath $P$ in the to-tree in $H \star F$ witnessing a global connection from $v$ to $a$. Since all edges incident to $Q$ have labels and $P$ contains at least one label and the smallest label is transferred to (v,a). Let $(x,y)$ be an edge in $P$ with smallest label $q_0$. Then this label is the index of a separator dipath $Q_0$ of an ascending digraph $H_0$ with dipath $P_0$ in $H_0$ which intersects $Q_0$. Then $H_0$ contains $H$ so all unlabeled edges in $P$ are in $H_0$. And all labeled edges in $P$ have labels at least as high as $q_0$. However, the higher the index of separator dipath then the younger a digraph it separates, so all other edges in $P$ have their endpoints connected by dipaths in digraphs equal to (or descending) from $H_0$, hence they are contained in $H_0$. Concatenating these edges and dipaths, including the above $P_0$ from $x$ to $y$, we get a dipath from $v$ to $a$ in $H_0$ which intersects $Q_0$ as desired.

Now return to a dipath query: when asking if $u$ reaches $w$ then a positive answer provides the index of a separator dipath $Q$ and global connections $(u,a)$ and $(b,w), a,b \in Q$ with a equal to or preceding b in $Q$. Now we set $sep(u,w) = q_0 = min\{sep(u,a), sep(b,w)\}$. The only surprising thing is that we do not need to consider the sep-values of the edges in the segment of $Q$ between a and b (that is, clearly an ascending digraph $H_0$ with separator dipath $Q_0$ indexed at $q_0$ such that $H_0$ contains dipaths from $u$ to $a$ and from $b$ to $w$, with one of these dipaths intersecting $Q_0$).

We need to argue that $H_0$ contains the segment of $Q$ from $a$ to $b$. Suppose for contradiction that some strict ancestor of $H_0$ had separator path $R$ that intersects this segment of $Q_0$. Since any separator path is a root path, R contains either $a$ or $b$ to $w$ which intersects $Q_0$ as desired.

Storing with each vertex the sep-values of the connections to and from each ascending separator dipath, we can compute the sep value of u,w in constant time, hence returning a simple dipath from u to w in time linear in its length using the method from basic recursion.

# Approximate Distance Oracles
We will generalise the approach from the previous section for approximate distances.

## $(3, \alpha)$-layered Digraphs
We define a **$(t,\alpha)$-layered spanning tree** T in a digraph H as a disoriented rooted spanning tree such that a path in T from the root is a concatenation of at most $t$ shortest dipaths in $H$ (each with length at most $\alpha$. We say $H$ is a $(t,\alpha)$-layered digraph if such a spanning tree exists.

**Lemma 3.2. **Given a digraph $G$ and scale $\alpha$, we can construct a series of digraphs satisfying:
- (i from 2.2) total number of edges and vertices in all the $G_i$ is linear in number of edges and vertices in $G$
- (iv from 2.2) $G_i$ is a minor of $G$ (made from deletion of edges, vertices and contractions of edges.
- Each vertex has an index $i(v)$ such that another vertex $w$ is at distance $d \leq \alpha$ from $v \in G$ iff $d$ is the smallest distance from $v$ to $w$ in $G^{\alpha}_{i(v)-2}, G^{\alpha}_{i(v)-1}$
- Each $G_i^{\alpha} = (V_i,E_i)$ is a $(3,\alpha)$-layered digraph with a $(3,\alpha)$-layered spanning tree denoted $T_i^{\alpha}$ with root denoted $r_i$
*Proof* Similar construction to Lemma 2.2. First partition vertices of $G$ into layers $L_0,...,L_k$. Let $L_0$ be the set of vertices reachable within a distance $\alpha$ from $v_0$ and for $i > 0$ we define $L_i$ as all vertices $v$ with shortest $v$ to $L_0,...,L_i$ distance less than $\alpha$ if $i$ odd, and if $i$ even we define $L_i$ as all vertices $v$ with shortest $L_0,...,L_i$ to $v$ distance less than $\alpha$. We define $k$ as first index such that $L_0,...,L_k = V$ and $i(v) = i$ for $v \in L_i$.

Each digraph $G_i^{\alpha}$ has three consecutive layers, with all preceding layers contracted into a single vertex. Define $r_0 = v_0$.

Proof of (i), (iv) are same as Lemma 2.2 and the proof of $(iii') is similar but we use shortest dipaths instead from (and to) $L_0,...,L_j$ to (and from) vertices when $j$ is even (odd). We suppress the root for connections for $i > 0$, which can be implemented by orienting all the edges incident on the root towards (or away from) the root if $i$ is odd (or even).

Observe that (ii') is satisfied. Consider arbitrary dipath $P$ from a vertex $v$ to a vertex $w$ with length at most $\alpha$. Consider innermost layer $L_i$ containing vertex $x$ from $P$. By definition of the layers if $j > i$ is even then $L_0,...,L_j$ contains the part of $P$ after $x$. If $j>i$ is odd then $L_0,...,L_j$ contains the part of $P$ before $x$. Then $P$ must be in $L_i \cup L_{i+1} \cup L_{i+2}$ hence $P$ is contained in $G_i^{\alpha}$. On the other hand since we know that $v \in P$ is only contained in $G_{i(v)-2}^{\alpha}, G_{i(v)-1}^{\alpha}, G_{i(v)}^{\alpha}$ so we conclude that $P$ from $v$ to $w$ is contained in one of these three digraphs.

Given a $(3, \alpha)$-layered digraph with its $(3,\alpha)$-layered rooted spanning tree $T_i^{\alpha}$, we can use this tree to find separators as we did previously, but with each root path being the concatenation of up to 3 shortest dipaths with length of at most $\alpha$.

## Representing Approximate Distances Via a Dipath
Given a digraph $G_i^{\alpha}$ containing a shortest dipath $Q$ from $s$ to $t$ with length at most $\alpha$. We want to represent distances $\leq \alpha$ via $Q$, accepting an additive error of $O(\epsilon \alpha)$ for a given $\epsilon \in (0,1]$.

### Approximation Connections to Q
Given a vertex $v$ and dipath $Q$, we may need several connections from $v$ to $Q$ to get a good approximation of distances from $v$ to $Q$. More precisely, a connection from $v$ to $Q$ is a new edge $(v,a) \in [v] \times V(Q)$. In this section, lengths = distances but later in efficient construction, some lengths will be longer. 

If $a$ equals or precedes $b$ in $Q$, $v$ is a vertex then we say a connection $(v,a)$ $\epsilon$-covers (v,b) if $l(v,a)+\delta (a,b) \leq \delta(v,b)+\epsilon \alpha$. $Q$ is a shortest path, so $\delta(a,b)$ is the distance from $a$ to $b$ in Q. We say a set $C(v,Q)$ of connections from $v$ to $Q$ is $\epsilon$-covering if it $\epsilon$-covers all pairs in $\{v\} \times V(Q)$ of distance at most $\alpha$. This gives us:

**Fact 3.3** Let $x$ be a vertex in $Q$ of distance at most $\alpha$ from $v$. If $C(v,Q)$ is $\epsilon$-covering there is a connection $(v,a) \in C(v,Q)$ such that $l(v,a)+\delta_Q(a,x) \leq \delta(v,x) + \epsilon \alpha$.

**Lemma 3.4** We want to argue that small $\epsilon$-covering sets exist. There is an $\epsilon$-covering set $C(v,Q)$ with size at most $\lceil 2/\epsilon \rceil$.

*Proof.* Take the first vertex in $Q$ within distance $\alpha$ from $v$, call it $a_0$. Make $(v,a_0)$ the first connection in $C(v,Q)$. Now scan remainining vertices $b$ in $Q$, adding connections only if some $(v,a)$ is the last connection and $(v,b)$ is not $\epsilon$-covered by $(v,a)$, i.e. add $b$ if $l(v,a) + \delta(a,b) > \delta(v,b) + \epsilon \alpha$.

Let $t$ be the last vertex in $Q$. When $(v,a)$ is the last connection added, consider the quantity $l(v,a) + \delta (a,t)$. When adding first connection, the quantity is $l(v,a_0)+\delta(a_0,t) \leq 2\alpha$. When we add $(v,b)$ to C(v,Q) we decrease this quantity by $(l(v,a)+\delta(a,t))-(l(v,b)+\delta(b,t)) = l(v,a)+\delta(a,b)-\delta(v,b) > \epsilon \alpha$. Since this quantity cannot be negative we can bound the number of connections added by $\lceil 2/\epsilon \rceil$.

### Approximate Distances via Q
Connections from $Q$ to $v$ are defined symmetric to the connections from $v$ to $Q$. If $(b,v)$ is a connection and $a$ precedes $b$ in $Q$ then $(b,v) \epsilon$-covers $(a,v)$ if $\delta(a,b)+l(b,v) \leq \delta(a,v)+\epsilon \alpha$. 

If $(u,a),(b,w)$ are connections from $u$ to $Q$ and from $Q$ to $q$ we define $dist((u,a),(b,w)) = l(u,a)+ \delta_Q(a,b) + l(b,w)$.

To compute $\delta_Q(a,b)$ efficiently we store with each vertex $c \in Q$ its distance $\delta(c,Q)$ from the start of $Q$, as well as its number $i(c,Q)$ in $Q$. Then $a$ equals or precedes $b$ in $Q$ if $i(a,Q) \leq i(b,Q)$ and then $\delta_Q(a,b) = d(b,Q) - d(a,Q)$. (note that we cannot directly compare $d(a,Q), d(b,Q)$ to determine if $a$ equals or precedes $b$ since there may be zero-weight edges in $Q$. If $i(a,Q) > i(b,Q)$ then we have $\delta_Q(a,b) = \infty$. If $C(u,Q), C(Q,w)$ are sets of connections from u to Q and from Q to w, we define $dist(C(u,Q),C(Q,w))=min_{(u,a) \in C(v,Q), (b,w) \in C(Q,w)} dist((u,a),(b,w))$.

If there are no connections from $u$ or to $w$ then we set $dist(C(u,Q),C(Q,w))=\infty$, so we always have $\delta(u,w) \leq dist(C(u,Q),C(Q,w))$.

**Lemma 3.5.** Suppose the shortest dipath from $u$ to $w$ is of length at most $\alpha$ and intersects $Q$. If $C(u,Q), C(Q,w)$ are $\epsilon$-covering, then $dist(C(u,Q),C(Q,w)) \leq \delta(u,w) + 2 \epsilon \alpha$.

*Proof.* Let $x$ be a vertex where the shortest dipath from $u$ to $w$ intersects $Q$. Since $\delta(u,x) \leq \alpha$ there is a connection $(u,a) \in C(u,Q)$ such that $l(v,a)+\delta_Q(a,x) \leq \delta(u,x)+\epsilon \alpha$. Symmetrically, we also have $(b,w) \in C(Q,w)$ such that $l(b,w)+\delta_Q(x,b) \leq \delta(x,w) + \epsilon \alpha$. Combining these inequalities with $dist(C(u,Q),C(Q,w)) \leq l(v,a)+\delta_Q(a,x)+l(b,w)+\delta_Q(x,b) \leq \delta(u,x) + \delta(x,w) + 2\epsilon \alpha = \delta(u,w) + 2\epsilon \alpha$.

We say $C(v,Q)$ is clean if there are no two distinct connections $(v,a), (v,b)$ such that $l(v,a) + \delta_Q(a,b) \leq l(v,b)$. Let $C(v,Q)$ be ordered if the connections are ordered according the the vertex-ordering in $Q$. Then $C(v,Q)$ is clean and ordered.

**Lemma 3.6.** If C(u,Q) and C(Q,w) are clean and ordered then we can determine $dist(C(u,Q),C(Q,w))$ in $O(|C(u,Q)|+|C(Q,w)|)$ time.

*Proof. *Finding the distance is just merging the two sets with ties resolved in favour of $C(u,Q)$, i.e. if $(u,c) \in C(u,Q), (c,w) \in C(Q,w)$ then we put $(u,c)$ ahead of $(c,w)$. We seek pairs $(u,a), (b,w)$ minimising the distance between them. Since $C(u,Q), C(Q,w)$ are clean we know that in this merged list the minimising distance vertices will be consecutive so we can find them in time linear to the size of both sets.

**Lemma 3.7.** Given a shortest dipath $Q$ of length at most $\alpha$ we can find $O(1/\epsilon)$ connections for each vertex such that if there is a shortest path from $u$ to $w$ of length at most $\alpha$ that intersects $Q$ then we can compute the distance from $u$ to $w$ in $O(1/\epsilon)$ time with an additive error of $O(\epsilon \alpha)$.

*Proof.* Combine Lemmas 3.4, 3.5, 3.6.

## Existence of Approximae Distance Oracles
To construct a scale-$(\alpha,O(\epsilon))$ distance oracle that approximates distances below $\alpha$ with additive error $O(\epsilon \alpha)$ we apply Lemma 3.7 to each dipath in the reachability construction and replace the previous reachability connections with new approximation connections.

Specifically, we run the recursion on each $(3, \alpha)$-layered graph $G_i^{\alpha}$ with framed separators as Section 2.5 details them. In each recursive call we have a subgraph $H$ of $G_i^{\alpha}$, a frame F, and a separator $S$ such that if $u,w$ are in different components of $H-S$ then any path from $u$ to $w$ in $G_i^{\alpha}$ intersects $F \cup S$. Because $F \cup S$ contains a constant number of root paths in the $(3, \alpha)$-layered spanning tree $T_i^{\alpha}$ and hence has a constant number of dipaths with length at most $\alpha$. 

We apply Lemma 3.7 to each dipaths, using $O(1/\epsilon)$ connections per vertex. We approximate the distance from $u$ to $w$ in $O(1/\epsilon)$ time with additive error of $O(\epsilon \alpha)$. Relative to the previous reachability construction, both space and query time blows up with a factor of $O(1/\epsilon)$.

**Lemma 3.8** We can construct a $O(n (log n)/\epsilon)$ space scale-$(\alpha, \epsilon)$ distance oracle approximating distances in $O(1/\epsilon)$ time.

Now we construct a stretch-$(1+\epsilon)$ distance oracle for $i = 1,...,\lceil \log_2{nN} \rceil,\alpha = 2^i$, and $\epsilon' \in \{1/2, \epsilon/4 \}$. First construct a scale-$(\alpha,\epsilon')$ distance oracle as above with $\epsilon' = 1/2$ with constant query time to approximate distances within a constant factor quickly. 

To approximate the $u$ to $w$ distance we binary search over the $\lceil \log_2{nN} \rceil$ values of $i$, looking for a value of $\alpha = 2^i$ such that $\alpha/4 = 2^{i-2} < \hat{\delta}^{(\alpha, 1/2)}(u,w) < \alpha = 2^i$, where the $\hat{\delta}^{(\alpha, \epsilon/4)}$ denotes the distance estimate by the scale-$(\alpha,\epsilon/4)$ distance oracle. This condition is always satisfied for $i = \rfloor \log_2{\delta(u,w)} \lfloor -1$ and sometimes also for $i = \rfloor \log_2{\delta(u,w)} \lfloor$. With this value of $\alpha$ we see that the estimate distance $\hat{\delta}^{(\alpha,\epsilon/4)}(u,w)$ will give us $\hat{\delta}^{(\alpha,\epsilon/4)}(u,w)/\delta(u,w) = 1+(\epsilon \alpha/4)/(\alpha/4) = 1+\epsilon$ with total query time $O(\log{\log{nN}}+1/\epsilon).

**Lemma 3.9.** We can construct a stretch-$(1+\epsilon)$ distance oracle using $O(\log{nN})$ scale-$(\alpha,\epsilon')$ distance oracles with $\alpha=2^i, i=0,...,\rceil \log_2{nN} \lceil, \epsilon' \in \{ 1/2, \epsilon/4 \}$. If a scale-$(\alpha,\epsilon')$ distance oracle approximates distances in time $t(\epsilon')$ independent of $\alpha$ then the stretch-$(1+\epsilon)$ distance oracle approximates distances in time $O(t(1/2)/\epsilon + t(\epsilon/4) \log \log{nN}). If the scale-$(\alpha,\epsilon')$ distance oracles are distributed on labels then the stretch-$(1+\epsilon)$ combines the labels for each vertex.

Combining the above two lemmas we get:

**Lemma 3.10.** We construct a stretch-(1+\epsilon)$ oracle using $O(n(\log{nN})(log n)/\epsilon)$ space which approximates distances in $O(log \log{nN} + 1/\epsilon)$ time, with the oracle distributed as a labeling scheme with labels of size $O((\log{nN})(log n)/\epsilon)$.

For an efficient construction of the oracle in Lemma 3.10 we need an efficient construction of covering connections (an analogy of Lemma 3.4).

## Construction Approximation Connections via a Dipath Efficiently
Given a digraph $H$ containing a shortest dipath $Q$ from $s$ to $t$ whose length is at most $\alpha$, we want to efficiently construct these $\epsilon$-covering sets of connections between $Q$ and each vertex in $H$.

We will focus on connections from $Q$ to vertices $v$ in $H$ with the implicit understanding of the symmetric connections from $v$ to $Q$. We will first construct $\epsilon$-covering sets of size $O((\log{n})/\epsilon)$ but will reduce the size using the following lemma.

**Lemma 3.11.** Given an ordered $\epsilon_0$-covering set $D(Q,v)$ of connections from $Q$ to $v$ we can construct a clean ordered $(\epsilon_0+\epsilon_1)$-covering set $C(Q,v) \subseteq D(Q,v)$ of size at most $1+(2+\epsilon_0)/\epsilon_1=O(1/\epsilon_1)$ in $O(|D(Q,v)|)$ time.

*Proof.* Generalisation of Lemma 3.4. First we delete any edge $(a,v) \in D(Q,v)$ with $l(a,v)> \alpha + \epsilon_0 \alpha$. With this done, we visit the connections of $D(q,v)$ in backwards order: the first connection $(c,v)$ always included in $C(Q,v)$. For any later connection $(a,v)$, let $(b,v)$ be the last connection added to $C(Q,v)$, then we only add $(a,v)$ if $\delta(a,b) + l(b,v) > l(a,v) + \epsilon \alpha$. To see that $C(Q,v)$ is $(\epsilon_0+\epsilon_1)-covering, consider any $a \in Q$ and let $b$ be a successor of $a$ in $Q$ such that $(b,v) \in D(Q,v)$ and $f(b)=\delta(a,b)+l(b,v)$ is minimised. 

Since $D(Q,v)$ is $\epsilon_0$-covering, $f(b) \leq \delta(a,v) + \epsilon_0 \alpha$. However, $(b,v)$ is excluded from $C(Q,v)$ if there is a $(c,v) \in C(Q,v)$ such that $\delta(b,c) + l(c,v) \leq l(b,v) + \epsilon_1 \alpha$. Then we know $\delta(a,c) + l(c,v) \leq \delta(a,b)+l(b,v)+\epsilon_1 \alpha = f(b) + \epsilon_1 \alpha \leq \delta(a,v)+(\epsilon_0+\epsilon_1)\alpha$.

To see that the size of $C(Q,v)$ is small, observe that when adding $(a,v)$ to $C(Q,v)$ we decrease the distance to $v$ from the first point $s$ in $Q$ by $> \epsilon_1 \alpha$. When $(b,v)$ is added more precisely, the decrease is by $(\delta(s,b)+l(b,v))-(\delta(s,a)+l(a,v))=\delta(a,b)+l(b,v)-l(a,v) > \epsilon_1 \alpha$. When the first connection $(c,v)$ was added this distance was at most $\delta(s,c) + l(c,v) \leq 2 \alpha + \epsilon_0 \alpha$, hence we can add at most $(2+\epsilon_0)/\epsilon_1$ additional connections.

Now we present an efficient way of constructing $\epsilon$-covering sets of size $O((\log{n})/\epsilon). To state the result formally let $sssp(Q,H)$ be the smallest number such that if $H_0$ is a subgraph of $H$, $Q_0$ is the reduction of $Q$ to vertices from $H_0$, and $b$ is any vertex in $Q_0$.

Then we compute the single-source shortest dipaths from $b$ in $H_0 \cup Q_0$ in $O(sssp(Q,H)|E(H_0)|)$ time. With a classic heap we know $sssp(Q,H) = O(log|V(H)|). If $H \cup Q$ is planar then $sssp(Q,H) = O(1)$, but this is not always true for our uses.

**Lemma 3.12.** Given a graph $H$ with shortest dipath $Q$, for each $v \in V(H)$ we can construct an ordered $\epsilon$-covering set $C(Q,v)$ of size $O((log|V(Q)|)/\epsilon)$ in $O(sssp(Q,H)|E(H)|(log|V(Q)|)/\epsilon)$ time.

To construct, we say that $(b,v) semi-$\epsilon$ covers $(a,v)$ if $a$ equals or precedes $b$ in $Q$ and $\delta(a,b)+l(b,v) \leq l(a,v)+\epsilon \alpha$. If $l(a,v)=\delta(a,v)$ then this is the same as $\epsilon$-covering but $l(b,v)$ may be larger than $\delta(b,v)$ — observe that semi-$\epsilon$-covering can be tested in constant time.

We use a recursion by taking $(Q_0,H_0)$ where $Q_0$ is a segment of $Q$ and $H_0$ is an induced subgraph of $H$ (contains all edges from $H$ between vertices in $H_0$). This recursion step will make some connections between interior vertices in $Q_0$ to vertices in $H_0$ (this recursion assumes that we always have a connection from an endpoint of $Q_0$ to all vertices in $H_0$. Although some of these endpoints may be infinite, they are still included.

To start we make a single source shortest path computation for each of the endpoints of $Q$, $s$ and $t$ and then for each $v \in V(H)$ we connect $s$ to $v$ with $l(s,v)=\delta(s,v)$ and $t$ to $v$ with $l(t,v)=\delta(t,v)$. Now we can recur on $(Q,H)$.

Given $(Q_0,H_0)$ we recur as follows: let $a$ be the first and $c$ be the last point in $Q_0$. Let $H*_0$ be the digraph consisting of $H_0, Q_0,$ and all connections from endpoints $a,c$ to vertices in $H_0$, and let $b$ be a vertex in the middle of $Q_0$ (if $Q_0$ has q vertices, then b is the $\rceil q/2 \lceil$ vertex in $Q_0$. After a single source shortest dipath computation from $b \in H*_0$, for each $v \in V(H_0)$, we connect $b$ to $v$ with $l(b,v)=\delta_{H*_0}(b,v).

Next let $Q_1$ be the part of $Q_0$ before $b$, and let $Q_2$ be the part after $b$. Let $U_1$ be the set of vertices $v$ with $l(a,v) > 2 \alpha$ or $(b,v)$ semi-$\epsilon$-covering (a,v). Then set $H_1=H_0 - U_1$ and $H_2 = H_0 - U_2$ and recur on $(Q_1,H_1), (Q_2,H_2)$.

### Correctness
Now we prove correctness. We claim: for $v \in V(H_0)$  and $d \in \{ a,b,c \}, l(d,v)=\delta_{H_0^{\star}}(d,v)$.

*Proof.* From the construction of $H_0^{\star}$ we immediately have $l(a,v) \geq \delta_{H_0^{\star}}(a,v)$ and $l(c,v) \geq \delta_{H_0^{\star}} (c,v)$. Also the new connections from $b$ satisfy this claim so it remains to prove that $l(a,v) \leq \delta_{H_0^{\star}}(a,v)$ and $l(c,v) \leq \delta_{H_0^{\star}}(a,v) and $l(c,v) \leq \delta_{H_0^{\star}}(c,v)$. This is true in the first recursive call, and it follows inductively for the subproblems because $H_1^{\star}$, $H_2^{\star}$ must give distances longer than $H_0^{\star}$.

(see iPad notes for proof of correctness)

### Number of Connections
We want to show that the number of connections to each vertex in $H$ is $O((log|V(Q)|)/\epsilon)$
