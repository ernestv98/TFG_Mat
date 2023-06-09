# APPROACH 2: endos of colored looped multidigraphs
# 1. Functions about colors
# 2. NO INV: C has no invertible elements
# 3. INV: C has exactly one involution








#--------------------------------------------------------------------------------------------------------------------------------------------
#   1
#--------------------------------------------------------------------------------------------------------------------------------------------

def edges_list(d): #convert d.edges() into a list of lists instead of a list of references to the original tuples
    edges = d.edges(sort=False) #If we don't specify argument sort a Warning appears. Our sorting choice only affects the sorting of parallel edges (edges are always sorted according to their vertices regardless of our choice here) so it should not matter. For more information read description of function .edges() in https://doc.sagemath.org/html/en/reference/graphs/sage/graphs/generic_graph.html#sage.graphs.generic_graph.GenericGraph.edges
    edges = [list(e) for e in edges]
    return edges

def edges_out_v(d, v): #returns a list with the outgoing colored arcs of v. d is not 3outreg
    edges = edges_list(d)
    outgoing_edges = []
    for edge in edges:
        if edge[0] == v:
            outgoing_edges.append(edge)
    return outgoing_edges

def parallel_edges(e1, e2):
    return e1[0] == e2[0] and e1[1] == e2[1]

def parallel_edges_v(d, v): #returns which are the parallel edges among the 3 outgoing edges of v. outdeg(v)=3. output can only be [], [0,1], [1,2] or [0,1,2] since edges are always ordered, so the case [0,2] does not exist
    edges_out = edges_out_v(d, v)
    n = d.order()
    k = 3
    if parallel_edges(edges_out[0], edges_out[1]):
        if parallel_edges(edges_out[2], edges_out[0]):
            return [0,1,2]
        return [0,1]
    if parallel_edges(edges_out[1], edges_out[2]):
        return [1,2]
    return []

def change_colors_v(d, v, colors, verbatim=False): #change colors of the 3 outgoing edges of v according to the list colors. outdeg(v)=3 but d is not 3-outreg
    k = 3
    if verbatim:
        print("··············································")
        print("adding colors", colors, "to vertex", v)
    #save old edges and delete them
    edges = edges_out_v(d, v)
    if verbatim:
        print("old_edges =", edges)
    d.delete_edges(edges)
    #compute new edges
    for i in range(k):
        edges[i][2] = colors[i]
    if verbatim:
        print("new_edges =", edges)
    #change edges
    d.add_edges(edges)
    if verbatim:
        print("··············································")


#Old way (2 functions): first make 3-outreg and then add colors
def fill_digraph(d, v=0):#repeats arcs so that it is 3-outregular. does all the possibilities. it is needed before applying add_colors_3outreg
    n = d.order()
    k = 3
    #initialize digraph with multiedges
    D = DiGraph(d, multiedges=True) #this way we can add repeated edges with function add_edge
    #stop if we have colored the outgoing edges of all the vertices
    if v == n:
        yield D
    else:
        #compute outgoing edges. outdegree can be 1, 2 or 3. if outdegree=3 we don't do anything (outdegree can't be 0 because we have already added loops)
        edges_out = edges_out_v(d, v)
        outdegree = len(edges_out)
        #if outdegree=1, we add the edge twice
        if outdegree == 1:
            D.add_edges([edges_out[0], edges_out[0]])
            yield from fill_digraph(D, v+1)
        #if outdegree=2 we have two options
        if outdegree == 2:
            D1 = D.copy()
            D1.add_edge(edges_out[0])
            yield from fill_digraph(D1, v+1)
            D2 = D.copy()
            D2.add_edge(edges_out[1])
            yield from fill_digraph(D1, v+1)
        #if outdegree=3 we don't do anything
        yield from fill_digraph(D, v+1)

def add_colors_3outreg(d, e, D_with_colors=DiGraph(multiedges=True,loops=True), v=0, verbatim=False): #colorations + add_colors_3outreg_old together, using that coloration[i] = edges[i][2]
    import itertools
    #check if D_with_colors is good so far
    #...
    #initializations
    if verbatim:
        print("//////////////////////////////////////////////////////////////////////////")
        print("Function with v = ", v)
    n = d.order()
    k = 3
    colors = list(range(k))
    if D_with_colors == DiGraph(multiedges=True,loops=True):
        D_with_colors = d.copy()
        if verbatim:
            print("Initializing D_with_colors")
    #stop if we have colored the outgoing edges of all the vertices
    if v == n:
        if verbatim:
            print("Done. Returning")
            print(edges_list(D_with_colors))
        yield D_with_colors
    else:
        #if we are at e, we only have one possibility
        if v == e:
            if verbatim:
                print("We are on the neutral element")
                print("colors e = ", colors)
            change_colors_v(D_with_colors, v, colors)
            yield from add_colors_3outreg(d, e, D_with_colors, v+1)
            if verbatim:
                print("//////////////////////////////////////////////////////////////////////////")
        #if we are not at e, put all possibilities
        else:
            parallel_edges = parallel_edges_v(D_with_colors, v)
            if verbatim:
                print("parallel_edges(", v, ") =", parallel_edges)
            #if there are 3 parallel edges, we have 1 possible coloring
            if parallel_edges == [0,1,2]:
                if verbatim:
                    print("Case A")
                    print("colors A = ", colors)
                change_colors_v(D_with_colors, v, colors)
                yield from add_colors_3outreg(d, e, D_with_colors, v+1)
                if verbatim:
                    print("//////////////////////////////////////////////////////////////////////////")
                    print("Function with v = ", v)
            #if there are 2 parallel edges, we have 2*3=6 possible colorings
            elif parallel_edges == [0,1]:  #the order is edge1, edge1, edge2
                if verbatim:
                    print("Case B")
                list_of_possible_colors_1 = [[0,1,2], [0,2,1], [1,2,0]]
                for possible_colors in list_of_possible_colors_1:
                    if verbatim:
                        print("colors B = ", possible_colors)
                    change_colors_v(D_with_colors, v, possible_colors)
                    yield from add_colors_3outreg(d, e, D_with_colors, v+1)
                    if verbatim:
                        print("//////////////////////////////////////////////////////////////////////////")
                        print("Function with v = ", v)
            elif parallel_edges == [1,2]: #the order is edge1, edge2, edge2
                if verbatim:
                    print("Case C")
                list_of_possible_colors_2 = [[0,1,2], [1,0,2], [2,0,1]]
                for possible_colors in list_of_possible_colors_2:
                    if verbatim:
                        print("colors C = ", possible_colors)
                    change_colors_v(D_with_colors, v, possible_colors)
                    yield from add_colors_3outreg(d, e, D_with_colors, v+1)
                    if verbatim:
                        print("//////////////////////////////////////////////////////////////////////////")
                        print("Function with v = ", v)
            #if there are no parallel edges we have 3!=6 possible colorings
            elif parallel_edges == []:
                if verbatim:
                    print("Case D")
                for perm_colors in itertools.permutations(colors):
                    if verbatim:
                        print("colors D = ", perm_colors)
                    change_colors_v(D_with_colors, v, perm_colors)
                    yield from add_colors_3outreg(d, e, D_with_colors, v+1)
                    if verbatim:
                        print("//////////////////////////////////////////////////////////////////////////")
                        print("Function with v = ", v)
            else:
                print("ERROR!!!")
                exit()

def add_colors_old(d, e): #fill_digraph + add_colors_3outreg together
    for d_3outreg in fill_digraph(d):
        for D_with_colors in add_colors_3outreg(d_3outreg, e):
            yield D_with_colors



#New way (1 function): make 3 outregular and add colors in the same function
def add_colors(d, e, D_with_colors=DiGraph(multiedges=True,loops=True), v=0, verbatim=False): #fill_digraph + add_colors_3outreg together
    import itertools
    #initializations
    n = d.order()
    k = 3
    colors = list(range(k))
    if D_with_colors == DiGraph(multiedges=True,loops=True):
        D_with_colors = d.copy()
    #check if partial coloring D_with_colors is good so far
    if not cycles_good(D_with_colors, e):
        if verbatim:
            print("partial coloring bad")
        yield None
    else:
        #stop if we have colored the outgoing edges of all the vertices
        if verbatim:
            print("partial coloring good")
        if v == n:
            if verbatim:
                print(edges_list(D_with_colors))
            yield D_with_colors
        else:
            #if we are at e, we only have one possibility
            if v == e:
                change_colors_v(D_with_colors, v, colors)
                yield from add_colors(d, e, D_with_colors, v+1)
            #if we are not at e, add colors to the 3 outgoing edges in all possible ways. If outdegree<3, repeat edges until outdegree=3 in all possible ways before adding colors.
            else:
                edges = edges_out_v(D_with_colors, v)
                outdeg = len(edges)
                if outdeg != D_with_colors.out_degree(v):
                    print("ERROR 0 (add_colors)")
                #if outdegree=1, fix it and call function at the same vertex v. we have 1 way to accomplish 3-outregularity
                if outdeg == 1:
                    if verbatim:
                        print("outdeg(", v, ") = 1")
                    edge = edges[0]
                    D_with_colors.add_edges([edge, edge])
                    yield from add_colors(d, e, D_with_colors, v)
                #if outdegree=2, fix it and call function at the same vertex v. we have 2 ways to accomplish 3-outregularity
                elif outdeg == 2:
                    if verbatim:
                        print("outdeg(", v, ") = 2")
                    edge1 = edges[0]
                    edge2 = edges[1]
                    #repeating edge 1
                    D_with_colors_1 = D_with_colors.copy()
                    D_with_colors_1.add_edge(edge1) #when looking at the edges the order will be edge1, edge1, edge2
                    yield from add_colors(d, e, D_with_colors_1, v)
                    #repeating edge 2
                    D_with_colors_2 = D_with_colors.copy()
                    D_with_colors_2.add_edge(edge2) #when looking at the edges the order will be edge1, edge2, edge2
                    yield from add_colors(d, e, D_with_colors_2, v)
                #if outdegree=3, add colors in all possible ways
                elif outdeg == 3:
                    parallel_edges = parallel_edges_v(D_with_colors, v)
                    if verbatim:
                        print("outdeg(", v, ") = 3")
                        print("parallel_edges(", v, ") =", parallel_edges)
                    #if there are 3 parallel edges, we have 1 possible coloring
                    if parallel_edges == [0,1,2]:
                        change_colors_v(D_with_colors, v, colors)
                        yield from add_colors(d, e, D_with_colors, v+1)
                    #if there are 2 parallel edges, we have 2*3=6 possible colorings
                    elif parallel_edges == [0,1]:  #the order is edge1, edge1, edge2
                        list_of_possible_colors_1 = [[0,1,2], [0,2,1], [1,2,0]]
                        for possible_colors in list_of_possible_colors_1:
                            change_colors_v(D_with_colors, v, possible_colors)
                            yield from add_colors(d, e, D_with_colors, v+1)
                    elif parallel_edges == [1,2]: #the order is edge1, edge2, edge2
                        list_of_possible_colors_2 = [[0,1,2], [1,0,2], [2,0,1]]
                        for possible_colors in list_of_possible_colors_2:
                            change_colors_v(D_with_colors, v, possible_colors)
                            yield from add_colors(d, e, D_with_colors, v+1)
                    #if there are no parallel edges we have 3!=6 possible colorings
                    elif parallel_edges == []:
                        for perm_colors in itertools.permutations(colors):
                            change_colors_v(D_with_colors, v, perm_colors)
                            yield from add_colors(d, e, D_with_colors, v+1)
                    else:
                        print("ERROR 1 (add_colors)")
                        exit()
                else:
                    print("ERROR 2 (add_colors)")
                    exit()






def subdigraph_color(d, color):
    subdigraph_col = DiGraph(multiedges=True, loops=True)
    for v in d.vertices(sort=True):
        subdigraph_col.add_vertex(v)
    for edge in edges_list(d):
        if edge[2] == color:
            subdigraph_col.add_edge(edge)
    return subdigraph_col

#checks cycles of colored orientations to discard bad colorations
def cycles_good(d, e, verbatim=False): #z is cycle length and l is cycle maximum distance
    from sage.graphs.connectivity import connected_component_containing_vertex
    for col in [0,1,2]:
        col_subgraph = subdigraph_color(d, col)
        #check if we have already colored the whole connected component of e (by checking if it has a cycle)
        we_have_colored_comp_e = False
        comp_e = d.subgraph(connected_component_containing_vertex(col_subgraph, e)) #it is the induced subgraph of vertices given by output of function connected_component_containing_vertex(col_subgraph, e)
        (z_e, Z_e) = comp_e.girth(certificate=True) #if certificate=True, gives the list of vertices of the cycle as the second component
        if verbatim:
            print("comp_e =", comp_e.vertices(sort=True))
            print("z_e =", z_e)
            print("Z_e =", Z_e)
        if z_e != Infinity: #to check that it has a cycle in a fast way (alternative: to use .is_forest())
            cycle_distance = []
            for w in Z_e:
                cycle_distance.append(comp_e.distance(e, w))
            l_e = min(cycle_distance)
            we_have_colored_comp_e = True
        #if so
        if we_have_colored_comp_e:
            #compute the cycle distances z and cycle lengths l we can
            for comp in col_subgraph.connected_components_subgraphs():
                if comp != comp_e:
                    (z, Z) = comp.girth(certificate=True)
                    if z != Infinity:
                        #check length
                        if z_e % z != 0: #checks that z_e is divisible by z
                            return False
                        #check distance
                        distances = []
                        for v in comp.vertices(sort=True):
                            if v not in Z:
                                cycle_distance = []
                                for w in Z:
                                    cycle_distance.append(comp.distance(v, w))
                                distances.append(min(cycle_distance))
                            else:
                                distances.append(0)
                        l = max(distances)
                        if l > l_e:
                            return False
    return True
    
    
    
    


#function that discards colorations with automorphisms (no invertible elements => no automorphisms other than id) (?)
#...




    
    
    
    
    






#--------------------------------------------------------------------------------------------------------------------------------------------
#   2
#--------------------------------------------------------------------------------------------------------------------------------------------

def is_color_endo(f,d):#returns True if all colors are preserved by the endomorphism
    for edge in edges_list(d):
        if not d.has_edge(f[edge[0]], f[edge[1]], edge[2]):
            return False
    return True

def digraph_endos_colors(d, e, f, v=0, verbatim=False): #generate only the digraph's endomporphisms that map some e to some c. We assume f is given such that f[e] = c, while the rest of f does not matter since it will be computed and overwritten. v states for the vertex we are analysing. We start with v = 0 and run through all the vertices until v=n. COLORS MUST BE RESPECTED BY ENDOMORPHISMS
    n = d.order()
    #stop if the function has run n times
    if v == n:
        #CHECKS THAT f PRESERVES COLORS
        if is_color_endo(f,d):
            if verbatim:
                print("good endo")
            yield f
        elif verbatim:
            print("bad endo")
    else:
        #if we are at e we don't change anything
        if v == e:
            yield from digraph_endos_colors(d, e, f, v+1)
        #if we are at a vertex u
        else:
            for u in d.vertices(sort=True):
                #try u as a candidate for f[v]
                if u >= f[v]:
                    u_is_bad = False
                    #check that out-neighbors are preserved by the endomorphism
                    for w in d.neighbors_out(v):
                        if w < v and not d.has_edge(u, f[w]):
                            u_is_bad = True
                            break
                    #check that in-neighbors are preserved by the endomorphism
                    if not u_is_bad:
                        for w in d.neighbors_in(v):
                            if w < v and not d.has_edge(f[w], u):
                                u_is_bad = True
                                break
                    #if u is a good candidate for f[v] go for the next vertex
                    if not u_is_bad:
                        f[v] = u
                        yield from digraph_endos_colors(d, e, f, v+1)
            f[v] = 0

def check_monoid_colors(d, e, verbatim=True):
    n = d.order()
    k = 3
    all0 = [0 for _ in range(n)]
    #initialize
    endos_M = []
    C = d.neighbors_out(e)
    #compute the monoid of color endomorphisms
    for v in range(n):
        seed_e_to_v = all0.copy()
        seed_e_to_v[e] = v
        for col_endo in digraph_endos_colors(d, e, seed_e_to_v):
            endos_M.append(col_endo)
    if len(endos_M) != n:
        return False
    #compute the corresponding digraph
    if verbatim:
        print("Monoid of size", len(endos_M), "=", n, "found!")
        print(endos_M)
    M = endos_M
    cay_M_C = cayley_graph(M, C_indices)
    if cay_M_C.is_isomorphic(d):
        print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
        print("M =", M)
        print("C =", C)
        print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
        return True
    return False

def check_monoid_colors_notgen(d, e, verbatim=True): #case C does not genretate M
    import itertools
    n = d.order()
    k = 3
    all0 = [0 for _ in range(n)]
    #initialize
    endos_M = []
    C = d.neighbors_out(e)
    #compute the monoid of color endomorphisms
    for v in range(k):
        seed_e_to_v = all0.copy()
        seed_e_to_v[e] = v
        for col_endo in digraph_endos_colors(d, e, seed_e_to_v):
            endos_M.append(col_endo)
    if verbatim:
        print("Enomorphisms monoid of size", len(endos_M))
    if len(endos_M) < n:
        return False
    #for each subset of n elements
    for M in itertools.combinations(endos_M, n):
        #compute the corresponding digraph
        if verbatim:
            print("Subonoid M of size", len(M), "found!")
            print(M)
        cay_M_C = cayley_graph(endos_M,C_indices)
        if underlying_graph(cay_M_C).is_isomorphic(underlying_graph(d)):
            print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
            print("M =", M)
            print("C =", C)
            print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
            return True
    
    return False

def MAIN_approach2(initial_line=1, step=1, verbatim=True, verbatim2=False): #puts loops, puts colors and checks monoid
    import time
    t2 = time.perf_counter()
    n = 14
    k = 3
    cnt = 0
    cnt_multiors_total = 240088032 #count_lines(fin) takes several minutes so I did it in advance and wrote the result here
    real_cnt = 0
    #read file with multiorientations of G72
    fin = open('G72_multiors_less_new.d6', 'r')
    line = fin.readline()
    #for every possible multiorientation
    while line:
        cnt += 1
        if cnt % step == initial_line % step:
            real_cnt += 1
            print("Multiorientation", cnt, "/", cnt_multiors_total)
            D = DiGraph(line,multiedges=True) #alternatively we could first do D = DiGraph(), then D.allow_multiple_edges(True) and then D = DiGraph(line)
            #for every possible addition of loops
            LIST_OF_D_WITH_LOOPS = add_loops(D)
            cnt_loops = 0
            for d in LIST_OF_D_WITH_LOOPS:
                if verbatim:
                    cnt_loops += 1
                    print("Multiorientation", cnt_multiors, "/", cnt_multiors_total, ". looping", cnt_loops, "/ ?")
                #for every neutral element candidate
                e_candidates = find_e_candidates_G72_loops(d)
                cnt_e = 0
                cnt_e_total = len(e_candidates)
                for e in e_candidates:
                    if verbatim:
                        cnt_e += 1
                        print("Multiorientation", cnt_multiors, "/", cnt_multiors_total, ". looping", cnt_loops, "/ ? . e candidate", cnt_e, "/", cnt_e_total)
                    #for every coloring
                    cnt_colors = 0
                    cnt_colors_total = pow(factorial(k), n-1)
                    for d_col in add_colors(d, e):
                        cnt_colors += 1
                        if verbatim:
                            print("Multiorientation", cnt_multiors, "/", cnt_multiors_total, ". looping", cnt_loops, "/ ? . e candidate", cnt_e, "/", cnt_e_total, ". coloring", cnt_colors, "/ aprox", cnt_colors_total)
                        if d_col != None:
                            if verbatim2:
                                print(edges_list(d_col))
                            #check_monoid_approach2
                            if check_monoid_colors(d_col, e):
                                return True
                            if verbatim2:
                                print("Not a monoid digraph.")
                                print("")
        line = fin.readline()
    fin.close()
    t2 = time.perf_counter()
    print("Number of lines analyzes:", real_cnt)
    print("Computation time:", t2-t1, "seconds")
    return False




    
                            
                            




#--------------------------------------------------------------------------------------------------------------------------------------------
#   3
#--------------------------------------------------------------------------------------------------------------------------------------------

def change_colors_v_and_refl_v(d, v, colors, refl, verbatim=False): #change colors of the 3 outgoing edges of v according to the list colors. outdeg(v)=3 but d is not 3-outreg. it also puts colors to the symmetrical edge refl(v)
    k = 3
    refl_v = refl(v)
    if verbatim:
        print("··············································")
        if refl_v != v:
            print("adding colors", colors, "to vertex", v, "and its reflection", refl_v)
        elif refl_v == v:
            print("adding colors", colors, "to vertex", v, ", which is its own reflection")
    #--------------
    #VERTEX v
    #--------------
    #save old edges and delete them
    edges = edges_out_v(d, v)
    if verbatim:
        print("old edges =", edges)
    d.delete_edges(edges)
    #compute new edges
    for i in range(k):
        edges[i][2] = colors[i]
    if verbatim:
        print("new edges =", edges)
    #change edges
    d.add_edges(edges)
    #--------------
    #VERTEX refl(v)
    #--------------
    if refl_v != v:
        #save old refl_edges and delete them
        old_refl_edges = edges_out_v(d, refl(v))
        if verbatim:
            print("old refl_edges =", old_refl_edges)
        d.delete_edges(old_refl_edges)
        #compute new refl_edges
        new_refl_edges = [[refl(edges[i][0]), refl(edges[i][1]), edges[i][2]] for i in range(k)]
        if verbatim:
            print("new refl_edges =", new_refl_edges)
        #change edges
        d.add_edges(new_refl_edges)
    if verbatim:
        print("··············································")

#Old way (2 functions): first make 3-outreg and then add colors SYMMETRICALLY. it assumes d is already symmetric.
def fill_digraph_INV(d, refl, v=0, verbatim=False):
    if verbatim:
        print("**********************************************")
    n = d.order()
    k = 3
    D = DiGraph(d, multiedges=True)
    #stop if we have filled the outgoing edges of all the vertices
    if v == n:
        yield D
        if verbatim:
            print("**********************************************")
    else:
        #compute outgoing edges. outdegree can be 1, 2 or 3. if outdegree=3 we don't do anything (outdegree can't be 0 because we have already added loops)
        edges_out = edges_out_v(d, v)
        outdegree = len(edges_out)
        #if outdegree=1, we add the edge twice
        if outdegree == 1:
            edge = edges_out[0]
            D.add_edges([edge, edge])
            if verbatim:
                print("edge =", edge)
            if refl(v) != v:
                refl_edge = (refl(edge[0]), refl(edge[1]))
                D.add_edges([refl_edge, refl_edge])
                if verbatim:
                    print("refl_edge =", refl_edge)
            yield from fill_digraph_INV(D, refl, v+1)
            if verbatim:
                print("**********************************************")
        #if outdegree=2 we have two options
        if outdegree == 2:
            D1 = D.copy()
            edge1 = edges_out[0]
            D1.add_edge(edge1)
            if verbatim:
                print("edge1 =", edge1)
            if refl(v) != v:
                refl_edge1 = (refl(edge1[0]), refl(edge1[1]))
                D1.add_edge(refl_edge1)
                if verbatim:
                    print("refl_edge1 =", refl_edge1)
            yield from fill_digraph_INV(D1, refl, v+1)
            if verbatim:
                print("**********************************************")
            D2 = D.copy()
            edge2 = edges_out[1]
            D2.add_edge(edge2)
            if verbatim:
                print("edge2 =", edge2)
            if refl(v) != v:
                refl_edge2 = (refl(edge2[0]), refl(edge2[1]))
                D2.add_edge(refl_edge2)
                if verbatim:
                    print("refl_edge2 =", refl_edge2)
            yield from fill_digraph_INV(D1, refl, v+1)
            if verbatim:
                print("**********************************************")
        #if outdegree=3 we don't do anything
        yield from fill_digraph_INV(D, refl, v+1)
        if verbatim:
            print("**********************************************")

def add_colors_3outreg_INV(d, e, refl, D_with_colors=DiGraph(multiedges=True,loops=True), i=0, vertices_to_be_done=[0,4,5,6,7,11,12,13], verbatim=False): #done are the reflections that have been done (we don't need to add v to done because we will never be at v again, so we only add refl(v) to done)
    import itertools
    if verbatim:
        print("//////////////////////////////////////////////////////////////////////////")
        print("i =", i)
    #initializations
    n = d.order()
    k = 3
    colors = list(range(k))
    if D_with_colors == DiGraph(multiedges=True,loops=True):
        D_with_colors = d.copy()
    #check if partial coloring D_with_colors is good so far
    if not cycles_good(D_with_colors, e):
        if verbatim:
            print("partial coloring bad")
        yield None
    else:
        if verbatim:
            print("partial coloring good")
        #stop if we have colored the outgoing edges of all the vertices
        if i == len(vertices_to_be_done):
            if verbatim:
                print("Done. Returning")
                print(edges_list(D_with_colors))
            yield D_with_colors
        else:
            v = vertices_to_be_done[i]
            if verbatim:
                print("Function with v = ", v)
            #if we are at e, we only have one possibility
            if v == e:
                if verbatim:
                    print("We are on the neutral element")
                    print("colors e = ", colors)
                change_colors_v_and_refl_v(D_with_colors, v, colors, refl)
                yield from add_colors_3outreg_INV(d, e, refl, D_with_colors, i+1)
                if verbatim:
                    print("//////////////////////////////////////////////////////////////////////////")
                    print("Function with v = ", v)
            #if we are not at e, put all possibilities
            else:
                parallel_edges = parallel_edges_v(D_with_colors, v)
                if verbatim:
                    print("parallel_edges(", v, ") =", parallel_edges)
                #if there are 3 parallel edges, we have 1 possible coloring
                if parallel_edges == [0,1,2]:
                    if verbatim:
                        print("Case A")
                        print("colors A = ", colors)
                    change_colors_v_and_refl_v(D_with_colors, v, colors, refl)
                    yield from add_colors_3outreg_INV(d, e, refl, D_with_colors, i+1)
                    if verbatim:
                        print("//////////////////////////////////////////////////////////////////////////")
                        print("Function with v = ", v)
                #if there are 2 parallel edges, we have 2*3=6 possible colorings
                elif parallel_edges == [0,1]:  #the order is edge1, edge1, edge2
                    if verbatim:
                        print("Case B")
                    list_of_possible_colors_1 = [[0,1,2], [0,2,1], [1,2,0]]
                    for possible_colors in list_of_possible_colors_1:
                        if verbatim:
                            print("colors B = ", possible_colors)
                        change_colors_v_and_refl_v(D_with_colors, v, possible_colors, refl)
                        yield from add_colors_3outreg_INV(d, e, refl, D_with_colors, i+1)
                        if verbatim:
                            print("//////////////////////////////////////////////////////////////////////////")
                            print("Function with v = ", v)
                elif parallel_edges == [1,2]: #the order is edge1, edge2, edge2
                    if verbatim:
                        print("Case C")
                    list_of_possible_colors_2 = [[0,1,2], [1,0,2], [2,0,1]]
                    for possible_colors in list_of_possible_colors_2:
                        if verbatim:
                            print("colors C = ", possible_colors)
                        change_colors_v_and_refl_v(D_with_colors, v, possible_colors, refl)
                        yield from add_colors_3outreg_INV(d, e, refl, D_with_colors, i+1)
                        if verbatim:
                            print("//////////////////////////////////////////////////////////////////////////")
                            print("Function with v = ", v)
                #if there are no parallel edges we have 3!=6 possible colorings
                elif parallel_edges == []:
                    if verbatim:
                        print("Case D")
                    for perm_colors in itertools.permutations(colors):
                        if verbatim:
                            print("colors D = ", perm_colors)
                        change_colors_v_and_refl_v(D_with_colors, v, perm_colors, refl)
                        yield from add_colors_3outreg_INV(d, e, refl, D_with_colors, i+1)
                        if verbatim:
                            print("//////////////////////////////////////////////////////////////////////////")
                            print("Function with v = ", v)
                else:
                    print("ERROR!!!")
                    exit()

def add_colors_INV_old(d, e, refl, verbatim=False): #fill_digraph + add_colors_3outreg together
    if verbatim:
        print(d.edges())
    for d_3outreg in fill_digraph_INV(d, refl):
        if verbatim:
            print(d_3outreg.edges())
        for D_with_colors in add_colors_3outreg_INV(d_3outreg, e, refl):
            yield D_with_colors



#New way (1 function): make 3 outregular and add colors in the same function
def add_colors_INV(d, e, refl, D_with_colors=DiGraph(multiedges=True,loops=True), i=0, vertices_to_be_done=[0,4,5,6,7,11,12,13], verbatim=False): #fill_digraph + add_colors_3outreg together
    import itertools
    if verbatim:
        print("//////////////////////////////////////////////////////////////////////////")
        print("i =", i)
    #initializations
    n = d.order()
    k = 3
    colors = list(range(k))
    if D_with_colors == DiGraph(multiedges=True,loops=True):
        D_with_colors = d.copy()
    #check if partial coloring D_with_colors is good so far
    if not cycles_good(D_with_colors, e):
        if verbatim:
            print("partial coloring bad")
        yield None
    else:
        #stop if we have colored the outgoing edges of all the vertices
        if verbatim:
            print("partial coloring good")
        if i == len(vertices_to_be_done):
            if verbatim:
                print("Done. Returning")
                print(edges_list(D_with_colors))
            yield D_with_colors
        else:
            v = vertices_to_be_done[i]
            if verbatim:
                print("Function with v = ", v)
            #if we are at e, we only have one possibility
            if v == e:
                if verbatim:
                    print("We are on the neutral element")
                    print("colors e = ", colors)
                change_colors_v_and_refl_v(D_with_colors, v, colors, refl)
                yield from add_colors_INV(d, e, refl, D_with_colors, i+1)
                if verbatim:
                    print("//////////////////////////////////////////////////////////////////////////")
                    print("i =", i)
                    print("Function with v = ", v)
            #if we are not at e, add colors to the 3 outgoing edges in all possible ways. If outdegree<3, repeat edges until outdegree=3 in all possible ways before adding colors.
            else:
                edges = edges_out_v(D_with_colors, v)
                outdeg = len(edges)
                if outdeg != D_with_colors.out_degree(v):
                    print("ERROR 0 (add_colors_INV)")
                #if outdegree=1, fix it and call function at the same vertex v. we have 1 way to accomplish 3-outregularity
                if outdeg == 1:
                    if verbatim:
                        print("**********************************************")
                        print("outdeg(", v, ") = 1")
                    edge = edges[0]
                    D_with_colors.add_edges([edge, edge])
                    if refl(v) != v:
                        refl_edge = (refl(edge[0]), refl(edge[1]))
                        D_with_colors.add_edges([refl_edge, refl_edge])
                    if verbatim:
                        print("**********************************************")
                    yield from add_colors_INV(d, e, refl, D_with_colors, i)
                    if verbatim:
                        print("//////////////////////////////////////////////////////////////////////////")
                        print("i =", i)
                        print("Function with v = ", v)
                #if outdegree=2, fix it and call function at the same vertex v. we have 2 ways to accomplish 3-outregularity
                elif outdeg == 2:
                    #repeating edge 1
                    if verbatim:
                        print("**********************************************")
                        print("outdeg(", v, ") = 2")
                        print("repeating edge 1")
                    D_with_colors_1 = D_with_colors.copy()
                    edge1 = edges[0]
                    D_with_colors_1.add_edge(edge1) #when looking at the edges the order will be edge1, edge1, edge2
                    if refl(v) != v:
                        refl_edge1 = (refl(edge1[0]), refl(edge1[1]))
                        D_with_colors_1.add_edge(refl_edge1)
                    if verbatim:
                        print("**********************************************")
                    yield from add_colors_INV(d, e, refl, D_with_colors_1, i)
                    if verbatim:
                        print("//////////////////////////////////////////////////////////////////////////")
                        print("i =", i)
                        print("Function with v = ", v)
                    #repeating edge 2
                    if verbatim:
                        print("**********************************************")
                        print("outdeg(", v, ") = 2")
                        print("repeating edge 2")
                    D_with_colors_2 = D_with_colors.copy()
                    edge2 = edges[1]
                    D_with_colors_2.add_edge(edge2) #when looking at the edges the order will be edge1, edge2, edge2
                    if refl(v) != v:
                        refl_edge2 = (refl(edge2[0]), refl(edge2[1]))
                        D_with_colors_2.add_edge(refl_edge2)
                    if verbatim:
                        print("**********************************************")
                    yield from add_colors_INV(d, e, refl, D_with_colors_2, i)
                    if verbatim:
                        print("//////////////////////////////////////////////////////////////////////////")
                        print("i =", i)
                        print("Function with v = ", v)
                #if outdegree=3, add colors in all possible ways
                elif outdeg == 3:
                    parallel_edges = parallel_edges_v(D_with_colors, v)
                    if verbatim:
                        print("outdeg(", v, ") = 3")
                        print("parallel_edges(", v, ") =", parallel_edges)
                    #if there are 3 parallel edges, we have 1 possible coloring
                    if parallel_edges == [0,1,2]:
                        if verbatim:
                            print("Case A")
                            print("colors A = ", colors)
                        change_colors_v_and_refl_v(D_with_colors, v, colors, refl)
                        yield from add_colors_INV(d, e, refl, D_with_colors, i+1)
                        if verbatim:
                            print("//////////////////////////////////////////////////////////////////////////")
                            print("i =", i)
                            print("Function with v = ", v)
                    #if there are 2 parallel edges, we have 2*3=6 possible colorings
                    elif parallel_edges == [0,1]:  #the order is edge1, edge1, edge2
                        if verbatim:
                            print("Case B")
                        list_of_possible_colors_1 = [[0,1,2], [0,2,1], [1,2,0]]
                        for possible_colors in list_of_possible_colors_1:
                            if verbatim:
                                print("colors B = ", possible_colors)
                            change_colors_v_and_refl_v(D_with_colors, v, possible_colors, refl)
                            yield from add_colors_INV(d, e, refl, D_with_colors, i+1)
                            if verbatim:
                                print("//////////////////////////////////////////////////////////////////////////")
                                print("i =", i)
                                print("Function with v = ", v)
                    elif parallel_edges == [1,2]: #the order is edge1, edge2, edge2
                        if verbatim:
                            print("Case C")
                        list_of_possible_colors_2 = [[0,1,2], [1,0,2], [2,0,1]]
                        for possible_colors in list_of_possible_colors_2:
                            if verbatim:
                                print("colors C = ", possible_colors)
                            change_colors_v_and_refl_v(D_with_colors, v, possible_colors, refl)
                            yield from add_colors_INV(d, e, refl, D_with_colors, i+1)
                            yield from add_colors_INV(d, e, refl, D_with_colors, i+1)
                            if verbatim:
                                print("//////////////////////////////////////////////////////////////////////////")
                                print("i =", i)
                                print("Function with v = ", v)
                    #if there are no parallel edges we have 3!=6 possible colorings
                    elif parallel_edges == []:
                        if verbatim:
                            print("Case D")
                        for perm_colors in itertools.permutations(colors):
                            if verbatim:
                                print("colors D = ", perm_colors)
                            change_colors_v_and_refl_v(D_with_colors, v, perm_colors, refl)
                            yield from add_colors_INV(d, e, refl, D_with_colors, i+1)
                            yield from add_colors_INV(d, e, refl, D_with_colors, i+1)
                            if verbatim:
                                print("//////////////////////////////////////////////////////////////////////////")
                                print("i =", i)
                                print("Function with v = ", v)
                    else:
                        print("ERROR 1 (add_colors_INV)")
                        exit()
                else:
                    print("ERROR 2 (add_colors_INV)")
                    exit()

def MAIN_approach2_INV(verbatim=False): #put loops symmetrically, put colors symmetrically and check monoid
    import time
    t1 = time.perf_counter()
    n = 14
    k = 3
    D = DiGraph('MOoIA?OOIA??OIA@?O@G?HGP@AGG?@Q?IO')
    e = 0
    g = D.automorphism_group() #order 2
    refl = g[1] #the involution
    freevertices = [4, 5, 6, 7, 11, 12, 13] #those that can have loops (and then per symmetry determine the rest)
    fin = open('G72involution.d6', 'r')
    fout = open('AA_output_MAIN_approach2_INV.txt', 'w')
    lines = fin.readlines()
    counter = 0
    counter_2 = 0
    for l in lines:
        counter += 1
        print("Checking line", counter, "of 1248")
        D = DiGraph(l, multiedges=True, loops=True) #alternatively we could do D=DiGraph(l), D.allow_multiple_edges(True), D.allow_loops(True)
        #put loops symmetrically
        for H in add_loops_INV(D, refl, freevertices):
            if len(H.loops()) > 0: #since G72 is a core, we know that there have to be loops when non-group semigroup graph
                counter_2 += 1
                #put colors symmetrically
                cnt_colors = 0
                cnt_colors_total = pow(factorial(k), n-1)
                for d_col in add_colors_INV(H, e, refl):
                    cnt_colors += 1
                    if d_col != None:
                        if verbatim:
                            print("coloring", cnt_colors, "/ aprox", cnt_colors_total)
                        if verbatim:
                            print(edges_list(d_col))
                        fout.write(str(edges_list(d_col))+"\n")
                        #check_monoid_approach2
                        if check_monoid_colors(d_col, e):
                            return True
                        if verbatim:
                            print("Not a monoid digraph.")
                            print("")
    fin.close()
    print("Number of digraphs analized:", counter_2)
    t2 = time.perf_counter()
    print("Computation time:", t2-t1, "seconds")
    return False

def MAIN_approach2_INV_2(verbatim=False): #put loops symmetrically, put colors symmetrically and check monoid
    import time
    t1 = time.perf_counter()
    n = 14
    k = 3
    D = DiGraph('MOoIA@OOI???OI?`?W@@?@GP@AGG?@Q?IO')
    e = 12
    g = D.automorphism_group() #order 2
    refl = g[1] #the involution
    freevertices = [0, 4, 5, 6, 7, 11, 13] #those that can have loops (and then per symmetry determine the rest)
    fin = open('G72involution_2.d6', 'r')
    fout = open('AA_output_MAIN_approach2_INV_2.txt', 'w')
    lines = fin.readlines()
    counter = 0
    counter_2 = 0
    for l in lines:
        counter += 1
        print("Checking line", counter, "of 528")
        D = DiGraph(l, multiedges=True, loops=True) #alternatively we could do D=DiGraph(l), D.allow_multiple_edges(True), D.allow_loops(True)
        #put loops symmetrically
        for H in add_loops_INV(D, refl, freevertices):
            if len(H.loops()) > 0: #since G72 is a core, we know that there have to be loops when non-group semigroup graph
                counter_2 += 1
                #put colors symmetrically
                cnt_colors = 0
                cnt_colors_total = pow(factorial(k), n-1)
                for d_col in add_colors_INV(H, e, refl):
                    cnt_colors += 1
                    if d_col != None:
                        if verbatim:
                            print("coloring", cnt_colors, "/ aprox", cnt_colors_total)
                        if verbatim:
                            print(edges_list(d_col))
                        fout.write(str(edges_list(d_col))+"\n")
                        #check_monoid_approach2
                        if check_monoid_colors(d_col, e):
                            return True
                        if verbatim:
                            print("Not a monoid digraph.")
                            print("")
    fin.close()
    print("Number of digraphs analized:", counter_2)
    t2 = time.perf_counter()
    print("Computation time:", t2-t1, "seconds")
    return False

def MAIN_approach2_INV_notgen(verbatim=False): #put loops symmetrically, put colors symmetrically and check monoid
    import time
    t1 = time.perf_counter()
    n = 14
    k = 3
    D = DiGraph('MOoIA?OOIA??OIA@?O@G?HGP@AGG?@Q?IO')
    e = 0
    g = D.automorphism_group() #order 2
    refl = g[1] #the involution
    freevertices = [4, 5, 6, 7, 11, 12, 13] #those that can have loops (and then per symmetry determine the rest)
    fin = open('G72involution.d6', 'r')
    fout = open('AA_output_MAIN_approach2_INV_notgen.txt', 'w')
    lines = fin.readlines()
    counter = 0
    counter_2 = 0
    for l in lines:
        counter += 1
        print("Checking line", counter, "of 1248")
        D = DiGraph(l, multiedges=True, loops=True) #alternatively we could do D=DiGraph(l), D.allow_multiple_edges(True), D.allow_loops(True)
        #put loops symmetrically
        for H in add_loops_INV(D, refl, freevertices):
            if len(H.loops()) > 0: #since G72 is a core, we know that there have to be loops when non-group semigroup graph
                counter_2 += 1
                #put colors symmetrically
                cnt_colors = 0
                cnt_colors_total = pow(factorial(k), n-1)
                for d_col in add_colors_INV(H, e, refl):
                    cnt_colors += 1
                    if d_col != None:
                        if verbatim:
                            print("coloring", cnt_colors, "/ aprox", cnt_colors_total)
                        if verbatim:
                            print(edges_list(d_col))
                        fout.write(str(edges_list(d_col))+"\n")
                        #check_monoid_approach2
                        if check_monoid_colors_notgen(d_col, e):
                            return True
                        if verbatim:
                            print("Not a monoid digraph.")
                            print("")
    fin.close()
    print("Number of digraphs analized:", counter_2)
    t2 = time.perf_counter()
    print("Computation time:", t2-t1, "seconds")
    return False


def MAIN_approach2_INV_notgen_2(verbatim=False): #put loops symmetrically, put colors symmetrically and check monoid
    import time
    t1 = time.perf_counter()
    n = 14
    k = 3
    D = DiGraph('MOoIA@OOI???OI?`?W@@?@GP@AGG?@Q?IO')
    e = 12
    g = D.automorphism_group() #order 2
    refl = g[1] #the involution
    freevertices = [0, 4, 5, 6, 7, 11, 13] #those that can have loops (and then per symmetry determine the rest)
    fin = open('G72involution_2.d6', 'r')
    fout = open('AA_output_MAIN_approach2_INV_notgen_2.txt', 'w')
    lines = fin.readlines()
    counter = 0
    counter_2 = 0
    for l in lines:
        counter += 1
        print("Checking line", counter, "of 528")
        D = DiGraph(l, multiedges=True, loops=True) #alternatively we could do D=DiGraph(l), D.allow_multiple_edges(True), D.allow_loops(True)
        #put loops symmetrically
        for H in add_loops_INV(D, refl, freevertices):
            if len(H.loops()) > 0: #since G72 is a core, we know that there have to be loops when non-group semigroup graph
                counter_2 += 1
                #put colors symmetrically
                cnt_colors = 0
                cnt_colors_total = pow(factorial(k), n-1)
                for d_col in add_colors_INV(H, e, refl):
                    cnt_colors += 1
                    if d_col != None:
                        if verbatim:
                            print("coloring", cnt_colors, "/ aprox", cnt_colors_total)
                        if verbatim:
                            print(edges_list(d_col))
                        fout.write(str(edges_list(d_col))+"\n")
                        #check_monoid_approach2
                        if check_monoid_colors_notgen(d_col, e):
                            return True
                        if verbatim:
                            print("Not a monoid digraph.")
                            print("")
    fin.close()
    print("Number of digraphs analized:", counter_2)
    t2 = time.perf_counter()
    print("Computation time:", t2-t1, "seconds")
    return False
