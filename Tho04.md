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

There is a dipath from $u$ to $w$ intersecting $Q$ iff $u$ connects to $a$ in $Q$ and $w$ connects from $b$ in $Q$ where $a$ equals of precedes $b$ in $Q$. (Assuming numbered vertices in $Q$ for checking precedence in constant time. 

<img width="492" alt="Screenshot 2022-10-11 at 14 15 05" src="https://user-images.githubusercontent.com/69584282/195168431-4aee8f08-359c-4634-9d79-7da897793867.png">

*Lemma 2.5.* For any digraph $H$ and dipath $Q$ we identify all connections between vertices in $H$ and dipath $Q$ in linear time.

*Proof.* We only need to identify connections from $Q$, which we do by recursion. Let $t$ be the last vertex in $Q$. Then using a BFS, we can find all vertices in $v$ reached by $t$. By definition each of these vertices connect from $t$ from $Q$. Now we remove all of these vertices (including $t$) from $H$ and $Q$, and recur on the remaining vertices. Observe that each edge is considered once so this is linear. Observe that if $t$ reaches a vertex $x \in Q$, $t$ reaches all the successors of $x \in Q$ so it is a 'suffix' (ending part) of $Q$ that we remove. So Q remains a dipath. If $P$ was a dipath from a vertex in $Q$ to a vertex $v$ and a vertex from $P$ is removed then observe that $t$ must reach $v$.

### Algorithm for $O(\log{n})$-query time Reachability Oracle
Let $G$ be a planar digraph. By Lemma 2.2 we reduce our problem to 2-layered digraphs. Consider a 2-layered digraph $H$ with a 2-layered rooted spanning tree $T$. Apply Lemma 2.3 to produce a separator $S$ with three root paths corresponding to six separator dipaths in $H$. With unit vertex weights we know each component of $C$ of $H-V(S)$ has at most half the weight of $H$.

For each dipath $Q \in S$ we apply Lemma 2.5 to produce all connections between $H,Q$. For each vertex $v$ we make two arrays: $to_v, from_v$, indexed by the separator dipath, where $to_v[Q]$ is the number of the vertex that $v$ connects to in $Q$ and $from_v[Q]$ is the number of the vertex that $v$ connects from. If $v$ does not reach $Q$ then $to_v[Q] = \infty$ and if $Q$ does not reach $v$ then $from_v[Q] = -1$. Then $u$ reaches $w$ via the separator $S$ iff $to_v[Q] \leq from_v[Q]$ for some dipath $Q \in S$. This takes constant time to check for given $Q$.

S is a connected part of the spanning tree $T$ including the root because it consists of root paths. Then contract $S$ into root vertex $r^S$, giving us a resulting 2-layered digraph $H/S$ with spanning tree $T/S$ rooted at $r^S$. We give $r^S$ zero weight because we are not interested in connections via $r^S$. For each component of $H-V(S)$ we recur on the subgraph $H' := C \cup \{r^S\}$. Because we give $r^S$ zero weight then total weight in $H' \leq 1/2$ total weight in $H$.

Using Lemma 2.3 (finding vertices such that each component of $H-V(T(u) \cup T(v) \cup T(w))$ has at most half weight of $H$) we find a separator $S'$ of $H'$, but we remove $r^S$ from $S', H'$ since it is suppressed when finding connections between vertices in $H'$ and dipaths in $S'$. At the next level of recursion we have components $C'$ of the graph $H-V(S')$ which are at most half the weight of $C$, so we get $O(\log{n})$ recursion calls with total runtime of $O(n \log{n})$.

### Indexing the Separator Dipaths
Each vertex $v$ takes parts in calls on a path in the recusion tree that goes from the root to where $v$ is selected for a separator $S$, which we call the *final call* of $v$. These numbers, used as indices for $to_v, from_v$ are $O(\log{n})$, which is also the size of these to and from tables for each vertex.

Let the dipaths in each separator of each call have a fixed ordering, which the enumeration by vertices participating in the call respects. Let $Q$ be a separator dipath in a call with $u$ and $w$, then $u$ and $w$ will use the same index for $Q$. To check reachability from $u \rightarrow w$ we only need to consider calls involving both vertices. **If the number of separator dipaths in calls like these are $s$, then $u$ reaches $w$ iff for some $q \in \{1,...,s\}$, $to_u[q] \leq from_w[q]$.** This check take $O(\log{n})$ time since $s = O(\log{n})$.

To find $s$ we store a separation number with each call $C$. The separation number is the number of separator dipaths in ancestor calls of (and including) $C$. So $s$ is the separation number of the nearest common ancestor call of the finall calls of $u, w$. Finding this nearest common ancestor is $O(\log{n})$ because our recursion tree is logarithmic in depth, so this is our overall query time for reachability.

### Reducing Query Time to $O(1)$
To achieve constant-time querying, we will pass down a set of root paths $F$ called the frame of $H$, that separate the subgraph $H$ from the rest of $G_i$. (This means $H$ will be a component of $G_i - V(F)$. Let $S$ be a separator of $H$ that separates $u,w$. Then $F \cup S$ separates $u,w$ in $G_i$. 

For each dipath $Q \in F \cup S$ we will identify the connections between $H,Q$ over $G_i$, such that $v \in V(H)$ connects to the first vertex in Q, and connects from the last vertex in Q that $v$ can reach in $G_i$. Since $F,S$ are constant in size we only have a constant number of separator and frame dipaths to query so we can check reachability from $u, w$.

The union of elements of $F$ is a tree of the same root as our rooted spanning tree. Since we want to minimise the number of root paths in $F$ we assume that these are root paths from leaves to tree, since additional root paths would not affect V(F) they are redundant. So we also call the root paths in $F$ the leaves of $F$.

### Few-frame Paths
We alternate between subgraph recursion (each of the new subgraphs have few vertices) and frame-reducing recursion (each new subgraph gets a frame with few leaves) to keep the frames constant in size.

Let $H+F$ be all of $H,F$ together with all the edges from $G_i$ between $H$ and $F$. Pick the separator $S =\{T(u) \cup T(v) \cup T(w)\} so that no component of $(H+F)-V(S)$ contains more than half the vertices in $H$. Applying Lemma 2.3, we know that we can find this by putting vertices in $H$ with weight 1, vertices in $F$ with weight 0.

In frame-reducing recursion we pick $S$ so no component of $(H+F)-V(S)$ contains more than half the leaves of $F$. Applying Lemma 2,3 in this case gives leaves with weight 1 and all other vertices get weight 0. Each of these recursion steps halves the weight of subgraph $H$ so we still only have logarithmic recursion steps.

We want to know how many root paths are in the frames passed down in recursion steps on the components of $H-V(S)$. Start with a subgraph reducing recursion: let original frame $F$ have $f$ root paths, then reach component receives a frame with at most $f+3$ root paths (those in $F$ and the three from $S$, the separator). For a frame-reducing recursion, we always pass down $S$ as a frame but can avoid passing down some of $F$'s root paths. Let $R \in F$ be a root path with leaf node $x$: when $R$ as a path intersects the separator $S$ then the rest of $R$ is contained in $S$. If $x \in S$ we do not need to include it as a separate root path, and only components of $H-V(S)$ with $x$ that need $R$ in their frame. Let $f'$ be the number of root paths currently in $F$. By our choice of $S$ (and Lemma 2.3), no component of $H-V(S)$ contains more than $f'/2$ leaves from F, and including the three root paths from $S$, we pass down at most $f'/2 +3$ root paths down in recursion.

The frame is empty in the root call on $G_i$. Generally, we go from $f \rightarrow$ at most $f+3$ to $(f+3)/2 +3 = f/2 + 4.5$ for one subgraph and one frame-reducing recursion. So the maximal number of frame paths for a subgraph reducing recursion if $f \leq 9$ and it is $f' \leq f+3 \leq 12$ for a frame-reducing recursion. These paths correspond to at most 2 dipaths in the frame.

### Reachability via Framed Separators
We need all connections over $G_i$ between $H$ and dipaths in frame $F$ and separator $S$ to answer reachability queries in $G_i$. Assume that all of the connections in $G_i$ between $H$ and the dipaths in the frame are passed down in recursive steps. Let $H \star F$ denote $H+F$ and the connections as edges. Let $u,w \in V(H)$, then $u$ reaches $w$ if and only if it does so in $H \star F$ (which is typically nonplanar, and these extra edges is linear in $n$ since each $v \in V(H)$ has one connection to and from the connection of each of the constant number of dipaths in $F$).

We aim to reduce $H \star F$ in size to something linear in number of edges of $G_i$ that are incident to vertices in $H$. We call a vertex in $F$ topological if it is an endpoint of a dipath in $F$ or a branching point between dipaths in $F$ (there are a constant number of these vertices). Let $v \in V(F)$ selected by H is it neighbours a vertex of $H$ in $H \star F$. Skipping vertices that are not topological or selected, if we have a segment of a dipath whose interior vertices are neither of the above then we contract it to a single edge. With this reduced $F$, we apply Lemma 2.5 (linear-time connection finding between digraph and dipath) to $H \star F$ and find all connections in $G_i$ between vertices in $H$ and dipaths in $S$.

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
