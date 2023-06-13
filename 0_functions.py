# 1. Common generic functions
# 2. Functions about Cayley graphs
# 3. Test functions






#--------------------------------------------------------------------------------------------------------------------------------------------
#   1
#--------------------------------------------------------------------------------------------------------------------------------------------


def count_lines(fin_name, verbatim=False): #counts the number of lines of a document
    fin = open(fin_name,'r')
    line = fin.readline()
    cnt = 0
    while line:
        cnt += 1
        if verbatim:
            print(cnt)
        line = fin.readline()
    fin.close()
    return cnt
    
def digraph_endos(G, e, f, v=0):#generate only the digraph's endomporphisms that map some e to some c. We assume f is given such that f[e] = c, while the rest of f does not matter since it will be computed and overwritten. v states for the vertex we are analysing. We start with v = 0 and run through all the vertices until v>n-1.
    n = G.order()
    #stop if we have computed all vertices from v=0 to v=n-1
    if v == n:
        if not outdeg_bad(G,f): #check the outdegree of f
            if not_invertible(G,f): #check that f is not invertible
                yield f
    else:
        #if we are at e we don't change anything
        if v == e:
            yield from digraph_endos_1(G, e, f, v+1)
        #if we are at a vertex u
        else:
            for u in G.vertices(sort=True):
                #try u as a candidate for f[v]
                if u >= f[v]:
                    u_is_bad = False
                    for w in G.neighbors_out(v):#check that out-neighbors are preserved by the endomorphism
                        if w < v and not G.has_edge(u, f[w]):
                            u_is_bad = True
                            break
                    if not u_is_bad:
                        for w in G.neighbors_in(v):#check that in-neighbors are preserved by the endomorphism
                            if w < v and not G.has_edge(f[w], u):
                                u_is_bad = True
                                break
                    #if u is a good candidate for f[v] go for the next vertex
                    if not u_is_bad:
                        f[v] = u
                        yield from digraph_endos_1(G, e, f, v+1)
            f[v] = 0

# e candidates before adding loops, when filtering the list of orientations to discard the very bad ones
def everybody_reachable_from_e(d, e_candidate):#check that all vertices v are reachable from e_candidate
    for v in d.vertices(sort=True):
        if d.distance(e_candidate, v) > d.order():
            return False
    return True

def there_is_e_candidate_G72(d): #check if there is any e candidate (in the case of no invertible elements)
    for v in d.vertices(sort=True):
        if d.out_degree(v) == 3 and d.in_degree(v) == 0:
            if everybody_reachable_from_e(d, v):
                return True
    return False
    
def there_is_e_candidate_G72_INV(d): #check if there is any e candidate (in the case of one involution)
    for v in d.vertices(sort=True):
        if d.out_degree(v) == 3 and d.in_degree(v) == 1:
            if everybody_reachable_from_e(d, v):
                return True
    return False


#Additional restictions on e candidats, when we have already put the loops
def exist_endos_from_e(d, e): #checks that from e there is an endo to every other vertex. (it is not equivalent to checking that everybody is reachable from e)
    n = d.order()
    f = [0 for _ in range(n)]
    #for each vertex (different to e)
    for v in range(n):
        if v != e:
            #compute endos that send e to v
            f[e] = v
            endos_list = digraph_endos(d, e, f)
            #discard bad endos
            good_endos_list = []
            for f_i in endos_list:
                if not outdeg_bad(d, f_i):
                    good_endos_list.append(f_i)
            #if good_endos_list is empty for one v, return False
            if not good_endos_list:
                return False
    #if endos_list is not empty for any v, return True
    return True
    
def find_e_candidates_G72_loops(d): #d already has loops
    candidates = []
    for v in d.vertices(sort=False):
        if v not in candidates:
            if d.out_degree(v) == 3 and d.in_degree(v) == 0:
                if everybody_reachable_from_e(d, v):
                    if exist_endos_from_e(d, v):
                        candidates.append(v)
    return candidates

def find_e_candidates_G72_loops_INV(d): #d already has loops
    candidates = []
    for v in d.vertices(sort=False):
        if v not in candidates:
            if d.out_degree(v) == 3 and d.in_degree(v) == 1:
                if everybody_reachable_from_e(d, v):
                    if exist_endos_from_e(d, v):
                        candidates.append(v)
    return candidates



#Loops
def add_loops(D, verbatim=False): #Add loops to multiorientations. Assumes that |C|=3, since assumes maximum outdegree = 3.
    #save the vertices that have out_degree 1 or 2 before adding any loops
    vertices_outdeg_1_2 = []
    for v in D.vertices(sort=True):
        if D.out_degree(v) == 1 or D.out_degree(v) == 2:
            vertices_outdeg_1_2.append(v)
    #for all vertices with outdegree 0 add loop
    D_essential_loops = DiGraph(D,loops=True)
    for v in D_essential_loops.vertices(sort=True):
        if D_essential_loops.out_degree(v) == 0:
            D_essential_loops.add_edge(v, v)
    #for some vertices with outdegree 1 or 2 add loop. Tries all possible subsets of vertices (using powerset) and returns all possible resulting digraphs
    done = []
    for V in powerset(vertices_outdeg_1_2):
        if verbatim:
            print("done =", done)
        #if we have not done an isomorphic set, do it
        if V not in done:
            if verbatim:
                print("V =", V)
            D_loops = D_essential_loops.copy()
            for v in V:
                D_loops.add_edge(v, v)
            yield D_loops
            #add to done all subsets isomorphic to V
            for phi in D.automorphism_group().list(): #automorphisms of the graph BEFORE adding loops
                phi_of_V = im_aut(phi,V)
                if phi_of_V not in done:
                    done.append(phi_of_V)
            





#--------------------------------------------------------------------------------------------------------------------------------------------
#   2
#--------------------------------------------------------------------------------------------------------------------------------------------

def underlying_graph(G): #make H the underlying graph of G
    H = Graph()
    #add to H the vertices
    for v in G.vertex_iterator():
        H.add_vertex(v)
    #add to H the edges but always in the same (arbitrary) direction. This way, different orientations look the same and therefore are added only once (the function add_edge automatically doesn't add repeated edges)
    for e in G.edge_iterator():
        if e[0] < e[1]:
            H.add_edge((e[0], e[1]))
        if e[0] > e[1]:
            H.add_edge((e[1], e[0]))
    return H

def cayley_graph(S, C, directed=False, verbatim=False): #Give the Cayley graph (not like a normal graph) given S and C, where M is a set of endos (it is assumed to have n distinct endos of size n, so not valid for all semigroups but it is valid for all monoids) and C is a set of of indices between 0 and len(M)-1. The output can have loops but not repeated edges
    n = len(S)
    order_of_C = len(C)
    if verbatim:
        print("n =", n)
        print("|C| =", order_of_C)
    if directed:
        G = DiGraph(loops=True)
    if not directed:
        G = Graph(loops=True)
    #add vertices and associate them with the elements of S
    for i in range(n):
        G.add_vertex(i)
        G.set_vertex(i, S[i]) #the function set_vertex associates an arbitrary object with a vertex. here we use it to store S in the vertices for us to recover S if we need it (using function semigroupfromcayley).
    #add edge i->m if m=i*c for some c in C, i.e. if S[m] = comp(S[i],S[c])
    for i in range(n):
        for j in C:
            x = comp(S[i], S[j])
            for m in range(n):
                if S[m] == x:
                    G.add_edge(i, m)
                    if verbatim:
                        print("[", i, ",", m, "]")
                    break
    return G

def semigroupfromcayley(G): #Give the semigroup S given a cayley graph G (see function cayley_graph)
    return [G.get_vertex(i) for i in range(G.order())]


def mtable_from_semigroup(S, e): #sorts the list of endomorphisms correctly so that they become the multiplication table. If m < n, returns partial table because it doesn't know which rows has to repeat to fill the empty rows, so it does not work for all semigroups. It does work for us since we look for monoids of size 14 and monoids don't have repeated rows, so n = m = 14 always.
    n = len(S[0])
    m = len(S) #for monoids m = n
    mtable = [[None for _ in range(n)] for _ in range(n)]
    #put in position i the endo that sends e to i
    for i in range(n):
        for j in range(m):
            if S[j][e] == i:
                mtable[i] = S[j]
                break
    return mtable
    


                
#--------------------------------------------------------------------------------------------------------------------------------------------
#   3
#--------------------------------------------------------------------------------------------------------------------------------------------

def test_G52_semigroups(): #gives error since program is not adapted to semigroups. useful to know what does and does not work.
    G52 = graphs.GeneralizedPetersenGraph(5,2)
    S_partial_1 = [ [1,2,3,4,5,0,7,8,6,9], [9,9,9,9,9,9,9,9,9,9] ]
    C_t1 = [0,1]
    S_partial_2 = [ [5,4,3,2,1,0,8,7,6,9], [3,2,1,0,5,4,6,8,7,9] , [9,9,9,9,9,9,9,9,9,9] ]
    C_t2 = [0,1,2]
    S1 = [ [0,1,2,3,4,5,6,7,8,9], [1,2,3,4,5,0,7,8,6,9], [2,3,4,5,0,1,8,6,7,9], [3,4,5,0,1,2,6,7,8,9], [4,5,0,1,2,3,7,8,6,9], [5,0,1,2,3,4,8,6,7,9], [9,9,9,9,9,9,9,9,9,9], [9,9,9,9,9,9,9,9,9,9] , [9,9,9,9,9,9,9,9,9,9] , [9,9,9,9,9,9,9,9,9,9]  ]
    C1 = [1,6]
    e1 = 0
    S2 = [ [5,4,3,2,1,0,8,7,6,9], [2,3,4,5,0,1,8,6,7,9], [1,0,5,4,3,2,7,6,8,9], [4,5,0,1,2,3,7,8,6,9], [3,2,1,0,5,4,6,8,7,9], [0,1,2,3,4,5,6,7,8,9], [9,9,9,9,9,9,9,9,9,9], [9,9,9,9,9,9,9,9,9,9] , [9,9,9,9,9,9,9,9,9,9] , [9,9,9,9,9,9,9,9,9,9]  ]
    C2 = [0,4,8]
    e2 = 5
    test_result = True
    #closure
    t1 = closure(S_partial_1)
    t1_sorted = mtable_from_semigroup(closure(S_partial_1), e1)
    if t1_sorted != S1:
        test_result = False
        print("test_G52_semigroups failed (ERROR 1)")
    t2 = closure(S_partial_2)
    t2_sorted = mtable_from_semigroup(closure(S_partial_2), e2)
    if t2_sorted != S2:
        test_result = False
        print("test_G52_semigroups failed (ERROR 2)")
    #cayley_graph and underlying_graph
    GS1 = cayley_graph(S1,C1)
    if not G52.is_isomorphic(underlying_graph(GS1)):
        test_result = False
        print("test_G52_semigroups failed (ERROR 3)")
    GS2 = cayley_graph(S2,C2)
    if not G52.is_isomorphic(underlying_graph(GS2)):
        test_result = False
        print("test_G52_semigroups failed (ERROR 4)")
    #closure, cayley_graph and underlying_graph
    G1 = cayley_graph(t1,C_t1)
    if not G52.is_isomorphic(underlying_graph(G1)):
        test_result = False
        print("test_G52_semigroups failed (ERROR 5)")
    #G1_bis = cayley_graph(t1_sorted,C1) #cannot be done because
    #if not G52.is_isomorphic(underlying_graph(G1_bis)):
    #    test_result = False
    #    print("test_G52_semigroups failed (ERROR 5_bis)")
    G2 = cayley_graph(t2,C_t2)
    if not G52.is_isomorphic(underlying_graph(G2)):
        test_result = False
        print("test_G52_semigroups failed (ERROR 6)")
    #G2_bis = cayley_graph(t2_sorted,C2)
    #if not G52.is_isomorphic(underlying_graph(G2)):
    #    test_result = False
    #    print("test_G52_semigroups failed (ERROR 6_bis)")
    #cayley_graph and semigroupfromcayley
    if S1 != semigroupfromcayley(GS1):
        test_result = False
        print("test_G52_semigroups failed (ERROR 7)")
    if S2 != semigroupfromcayley(GS2):
        test_result = False
        print("test_G52_semigroups failed (ERROR 8)")
    #closure, cayley_graph and semigroupfromcayley
    if t1 != semigroupfromcayley(G1):
        test_result = False
        print("test_G52_semigroups failed (ERROR 9)")
    #if t1_sorted != semigroupfromcayley(G1_bis):
    #    test_result = False
    #    print("test_G52_semigroups failed (ERROR 9_bis)")
    if t2 != semigroupfromcayley(G2):
        test_result = False
        print("test_G52_semigroups failed (ERROR 10)")
    #if t2_sorted != semigroupfromcayley(G2_bis):
    #    test_result = False
    #    print("test_G52_semigroups failed (ERROR 10_bis)")
    return test_result

def test_G52_monoids():
    G52 = graphs.GeneralizedPetersenGraph(5,2)
    M_partial_1 = [ [1,2,3,4,5,0,7,8,6,9], [6,6,6,6,6,6,9,9,9,9] ]
    C_t1 = [0,1]
    M_partial_2 = [ [5,4,3,2,1,0,8,7,6,9], [3,2,1,0,5,4,6,8,7,9], [8,8,8,8,8,8,9,9,9,9] ]
    C_t2 = [0,1,2]
    M1 = [ [0,1,2,3,4,5,6,7,8,9], [1,2,3,4,5,0,7,8,6,9], [2,3,4,5,0,1,8,6,7,9], [3,4,5,0,1,2,6,7,8,9], [4,5,0,1,2,3,7,8,6,9], [5,0,1,2,3,4,8,6,7,9], [6,6,6,6,6,6,9,9,9,9], [7,7,7,7,7,7,9,9,9,9], [8,8,8,8,8,8,9,9,9,9], [9,9,9,9,9,9,9,9,9,9] ]
    C1 = [1,6]
    e1 = 0
    M2 = [ [5,4,3,2,1,0,8,7,6,9], [2,3,4,5,0,1,8,6,7,9], [1,0,5,4,3,2,7,6,8,9], [4,5,0,1,2,3,7,8,6,9], [3,2,1,0,5,4,6,8,7,9], [0,1,2,3,4,5,6,7,8,9], [6,6,6,6,6,6,9,9,9,9], [7,7,7,7,7,7,9,9,9,9], [8,8,8,8,8,8,9,9,9,9], [9,9,9,9,9,9,9,9,9,9] ]
    C2 = [0,4,8]
    e2 = 5
    test_result = True
    #closure
    t1 = closure(M_partial_1)
    t1_sorted = mtable_from_semigroup(closure(M_partial_1), e1)
    if t1_sorted != M1:
        test_result = False
        print("test_G52_monoids failed (ERROR 1)")
    t2 = closure(M_partial_2)
    t2_sorted = mtable_from_semigroup(closure(M_partial_2), e2)
    if t2_sorted != M2:
        test_result = False
        print("test_G52_monoids failed (ERROR 2)")
    #cayley_graph and underlying_graph
    GM1 = cayley_graph(M1,C1)
    if not G52.is_isomorphic(underlying_graph(GM1)):
        test_result = False
        print("test_G52_monoids failed (ERROR 3)")
    GM2 = cayley_graph(M2,C2)
    if not G52.is_isomorphic(underlying_graph(GM2)):
        test_result = False
        print("test_G52_monoids failed (ERROR 4)")
    #closure, cayley_graph and underlying_graph
    G1 = cayley_graph(t1,C_t1)
    if not G52.is_isomorphic(underlying_graph(G1)):
        test_result = False
        print("test_G52_monoids failed (ERROR 5)")
    G1_bis = cayley_graph(t1_sorted,C1)
    if not G52.is_isomorphic(underlying_graph(G1_bis)):
        test_result = False
        print("test_G52_monoids failed (ERROR 5_bis)")
    G2 = cayley_graph(t2,C_t2)
    if not G52.is_isomorphic(underlying_graph(G2)):
        test_result = False
        print("test_G52_monoids failed (ERROR 6)")
    G2_bis = cayley_graph(t2_sorted,C2)
    if not G52.is_isomorphic(underlying_graph(G2)):
        test_result = False
        print("test_G52_monoids failed (ERROR 6_bis)")
    #cayley_graph and semigroupfromcayley
    if M1 != semigroupfromcayley(GM1):
        test_result = False
        print("test_G52_monoids failed (ERROR 7)")
    if M2 != semigroupfromcayley(GM2):
        test_result = False
        print("test_G52_monoids failed (ERROR 8)")
    #closure, cayley_graph and semigroupfromcayley
    if t1 != semigroupfromcayley(G1):
        test_result = False
        print("test_G52_monoids failed (ERROR 9)")
    if t1_sorted != semigroupfromcayley(G1_bis):
        test_result = False
        print("test_G52_monoids failed (ERROR 9_bis)")
    if t2 != semigroupfromcayley(G2):
        test_result = False
        print("test_G52_monoids failed (ERROR 10)")
    if t2_sorted != semigroupfromcayley(G2_bis):
        test_result = False
        print("test_G52_monoids failed (ERROR 10_bis)")
    return test_result

def test_G62_monoids():
    G62 = graphs.GeneralizedPetersenGraph(6,2)
    M_partial_1 = [ [1,2,3,4,5,0,9,8,11,10,7,6], [8,10,6,8,10,6,8,8,10,10,6,6] ]
    C_t1 = [0,1]
    M1 = [ [0,1,2,3,4,5,6,7,8,9,10,11], [1,2,3,4,5,0,9,8,11,10,7,6], [2,3,4,5,0,1,10,11,6,7,8,9], [3,4,5,0,1,2,7,6,9,8,11,10], [4,5,0,1,2,3,8,9,10,11,6,7], [5,0,1,2,3,4,11,10,7,6,9,8], [6,8,10,6,8,10,6,6,8,8,10,10], [7,9,11,7,9,11,7,7,9,9,11,11], [8,10,6,8,10,6,8,8,10,10,6,6], [9,11,7,9,11,7,9,9,11,11,7,7], [10,6,8,10,6,8,10,10,6,6,8,8], [11,7,9,11,7,9,11,11,7,7,9,9] ]
    C1 = [1,8]
    e1 = 0
    test_result = True
    #closure
    t1 = closure(M_partial_1)
    t1_sorted = mtable_from_semigroup(t1, e1)
    if t1_sorted != M1:
        test_result = False
        print("test_G62_monoids failed (ERROR 1)")
    #cayley_graph and underlying_graph
    GM1 = cayley_graph(M1,C1)
    if not G62.is_isomorphic(underlying_graph(GM1)):
        test_result = False
        print("test_G62_monoids failed (ERROR 2)")
    #closure, cayley_graph and underlying_graph
    G1 = cayley_graph(t1,C_t1)
    if not G62.is_isomorphic(underlying_graph(G1)):
        test_result = False
        print("test_G62_monoids failed (ERROR 3)")
    G1_bis = cayley_graph(t1_sorted,C1)
    if not G62.is_isomorphic(underlying_graph(G1_bis)):
        test_result = False
        print("test_G62_monoids failed (ERROR 3_bis)")
    #cayley_graph and semigroupfromcayley
    if M1 != semigroupfromcayley(GM1):
        test_result = False
        print("test_G62_monoids failed (ERROR 4)")
    #closure, cayley_graph and semigroupfromcayley
    if t1 != semigroupfromcayley(G1):
        test_result = False
        print("test_G62_monoids failed (ERROR 5)")
    if t1_sorted != semigroupfromcayley(G1_bis):
        test_result = False
        print("test_G62_monoids failed (ERROR 5_bis)")
    return test_result

def test_aut():
    G1 = DiGraph([[0,1],[(0,1)]]) #has one automorphism (the identity)
    G2 = DiGraph([[0,1],[(0,1),(1,0)]]) #has two automorphisms (the identity and to send one vertex to the other)
    if len(G1.automorphism_group().list()) != 1:
        return False
    if len(G2.automorphism_group().list()) != 2:
        return False
    return True

def test_loops(): #for more clarity, put verbatim=True in function add_loops
    C5 = graphs.CycleGraph(5)
    D5 = DiGraph(C5)
    looped_graphs = []
    for d in add_loops(D5):
        looped_graphs.append(d)
    if len(looped_graphs) == 8:
        return True
    return False







#tests about colors

def test_add_colors_old_1(verbatim=False):
    V = [0, 1, 2, 3, 4]
    E = [(0,1), (0,2), (0,3), (1,1), (1,1), (1,1), (2,0), (2,0), (2,3), (3,1), (3,2), (3,2), (4,1), (4,2), (4,4)]
    d = DiGraph([V,E], multiedges=True, loops=True)
    if verbatim:
        print("original edges =" , edges_refs(d))
    e = 0
    done = []
    cnt = 0
    total_cnt = 1*1*3*3*6
    for D_col in add_colors_old(d, e):
        cnt += 1
        edges = edges_list(D_col)
        if verbatim:
            print("----------------------------------------------------------------------")
            print("done =", done)
            print("edges =", edges)
            print("----------------------------------------------------------------------")
        if edges in done:
            print("ERROR 1 (test_add_colors)", "( cnt =", cnt, ")")
            return False
        done.append(edges)
        if verbatim:
            D_col.plot(color_by_label=True)
    if cnt != total_cnt:
        print("ERROR 2 (test_add_colors)")
        return False
    return True

def test_add_colors_1(verbatim=False):
    V = [0, 1, 2, 3, 4]
    E = [(0,1), (0,2), (0,3), (1,1), (1,1), (1,1), (2,0), (2,0), (2,3), (3,1), (3,2), (3,2), (4,1), (4,2), (4,4)]
    d = DiGraph([V,E], multiedges=True, loops=True)
    e = 0
    done = []
    cnt = 0
    total_cnt = 1*1*3*3*6
    for D_col in add_colors(d, e):
        cnt += 1
        edges = edges_list(D_col)
        if verbatim:
            print("----------------------------------------------------------------------")
            print("done =", done)
            print("edges =", edges)
            print("----------------------------------------------------------------------")
        if edges in done:
            print("ERROR 1 (test_add_colors)", "( cnt =", cnt, ")")
            return False
        done.append(edges)
        if verbatim:
            D_col.plot(color_by_label=True)
    if cnt != total_cnt:
        print("ERROR 2 (test_add_colors)")
        return False
    return True

def test_add_colors_old_2(N=1000, verbatim=False): #tests if add_colors_old gives different colorings (checks only the first N colorings)
    cnt = 0
    done = []
    fin = 'G72_multiors_less_new.d6'
    #read file with multiorientations of G72
    fin = open(fin, 'r')
    line = fin.readline()
    #for every possible multiorientation
    while line:
        D = DiGraph(line,multiedges=True)
        #for every possible addition of loops
        LIST_OF_D_WITH_LOOPS = add_loops(D)
        for d in LIST_OF_D_WITH_LOOPS:
            #for every neutral element candidate
            e_candidates = find_e_candidates_G72_loops(d)
            for e in e_candidates:
                #for every coloring
                for d_col in add_colors_old(d, e):
                    if d_col != None:
                        cnt += 1
                        if verbatim:
                            print(cnt)
                        if cnt > N:
                            return True
                        colored_edges = edges_list(d_col)
                        if colored_edges in done:
                            return False
                        done.append(colored_edges)
                        
        line = fin.readline()
    fin.close()
    
def test_add_colors_2(N=1000, verbatim=False): #tests if add_colors_new gives different colorings (checks only the first N colorings)
    cnt = 0
    done = []
    fin = 'G72_multiors_less_new.d6'
    #read file with multiorientations of G72
    fin = open(fin, 'r')
    line = fin.readline()
    #for every possible multiorientation
    while line:
        D = DiGraph(line,multiedges=True)
        #for every possible addition of loops
        LIST_OF_D_WITH_LOOPS = add_loops(D)
        for d in LIST_OF_D_WITH_LOOPS:
            #for every neutral element candidate
            e_candidates = find_e_candidates_G72_loops(d)
            for e in e_candidates:
                #for every coloring
                for d_col in add_colors(d, e):
                    if d_col != None:
                        cnt += 1
                        if verbatim:
                            print(cnt)
                        if cnt > N:
                            return True
                        colored_edges = edges_list(d_col)
                        if colored_edges in done:
                            return False
                        done.append(colored_edges)
                        
        line = fin.readline()
    fin.close()

def tests_colors():
    color_tests = [test_add_colors_1(), test_add_colors_2(), test_add_colors_old_1(), test_add_colors_old_2]
    m = len(color_tests)
    for i in range(m):
        if not color_tests[i]:
            print("Test", i, "failed")
            return False
    return True


def tests():
    list_of_tests = [test_G52_monoids(), test_G62_monoids() , test_aut(), test_loops()]
    m = len(list_of_tests)
    for i in range(m):
        if not list_of_tests[i]:
            print("Test", i, "failed")
            return False
    return True
