# APPROACH 1: endos of looped multidigraphs
# 1. Functions about endos
# 2. NO INV: C has no invertible elements
# 3. INV: C has exactly one involution







#--------------------------------------------------------------------------------------------------------------------------------------------
#   1
#--------------------------------------------------------------------------------------------------------------------------------------------

def im(f, V): #image of the set of vertices V by the endomorphism f. f is a list
    im = set()
    for v in V:
        im.add(f[v])
    return list(im)

def im_BIS(f, V): #not using it because it probably is slower
    return [f[v] for v in V]

def im_aut(phi, V): #image of the set of vertices V by the automorphism phi. phi is not a list (see the format of the output of .automorphism_group()), so we have phi(v) instead of phi[v]
    im = set()
    for v in V:
        im.add(phi(v))
    return list(im)

def im_aut_BIS(phi, V): #not using it because it probably is slower
    return [phi(v) for v in V]

def comp(f, g): #composition of two endomorphisms
    return [f[g_i] for g_i in g]

def outdeg_bad(d, f): #checks that the image of f has no outgoing arcs. The outdegree is bad when there are outgoing arcs.
    im_f = im(f,d.vertices(sort=True))
    for v in im_f:
        for w in d.neighbors_out(v):
            if w not in im_f:
                return True
    return False

def not_invertible(d,f): #checks if f is not invertible by checking that the image of f is not of size n=d.order()  
    return len(im(f,d.vertices(sort=True))) < d.order()

def closure(S_original, top_s=0, m=0, verbatim=False): #closure of k endomorfisms S of an n-vertex graph, aborts when there are more than top_s endomorphisms already. When the function calls itself, m is the number of endomorphisms that have been added and have to be done.
    S = S_original.copy()
    k = len(S)
    n = len(S[0])
    if verbatim:
        print("S =", S)
        print("n =", n)
        print("k =", k)
    #initialize top_s
    if top_s == 0:
        top_s = n
    #if S already has more endomorphisms than the maximum number of endomorphisms, stop
    if k > top_s:
        if verbatim:
            print("Too many endomorphisms...")
        S.append("...")
        return S
    #initialize todo (m=0 only occurs the first time we call the function and all the combinations have to be done. m!=0 is when we added m endomorphisms and we only have to do them). todo does not change along the function because if it changes the "for j in todo[i]" messes up (i don't know why, but it happened and i had to change it)
    todo = []
    if m == 0:
        for i in range(k):
            todo.append(list(range(k)))
    if m != 0:
        for i in range(k-m):
            todo.append(list(range(k-m, k)))
        for i in range(k-m, k):
            todo.append(list(range(k)))
    if verbatim:
        print("todo = ", todo)
    #compute more endomorphisms composing the existing endomorphisms
    new_k = k
    for i in range(k):
        if verbatim:
            print("i =", i)
            print("todo[", i, "] = ", todo[i])
        for j in todo[i]:
            if verbatim:
                print("j = ", j)
            #build new endo as a composition of S[i] and S[j] and check if it is equal to one of the previous ones
            h = comp(S[i], S[j])
            new_endo = True
            for l in range(new_k):
                if verbatim:
                    print("l = ", l)
                if h == S[l]:
                    new_endo = False
                    if verbatim:
                        print("repeated_endo")
                    break
            if new_endo:
                if verbatim:
                    print("new_endo")
                S.append(h)
                new_k += 1
                if (new_k > top_s):
                    if verbatim:
                        print("Too many endomorphisms...")
                    S.append("...")
                    return S
    if verbatim:
        print("all i,j checked")
    #if we haven't added any new endomorphisms, stop
    if new_k == k:
        if verbatim:
            print("Closure completed.")
        return S
    #if we have added some endomorphisms, repeat the process
    else:
        if verbatim:
            print("new endos added, starting again")
        return closure(S, top_s, new_k-k, verbatim)

def canbepartial(t):#discard partial "multipliaction table" set if every column has a repetition, i.e., for all i\in[n] there are f,g: f(i)=g(i), becasue then there can be no right-neutral-element
    n = len(t[0])
    if len(t) > n:
        return False
    #initialize a matrix of zeros (all00) and a vector of ones (lines_ok)
    all00 = [[0 for _ in range(n)] for _ in range(n)]
    lines_ok = [1 for _ in range(n)]
    #put a 0 in lines_ok[i] if f[i] = g[i] for some f,g in t (the two endomorphisms can be a different pair for every i)
    for i in range(n):
        for f in t:
            if all00[i][f[i]] == 0:
                all00[i][f[i]] = 1
            else:
                lines_ok[i] = 0
    #return False if for every i there are two coinciding endomorphisms of t
    for i in range(n):
        if lines_ok[i] == 1:
            return True
    return False
 
def canbepartial_BIS(t): #does the same in a more comprehensible way but also more inefficient way. it is useful to check that the other works
    n = len(t[0])
    k = len(t)
    if k > n:
        return False
    #initialize a vector of ones (lines_ok)
    lines_ok = [1 for _ in range(n)]
    #put a zero in lines_ok[i] if there are two endos in t with the same value at i
    for i in range(n):
        for j1 in range(k):
            for j2 in range(j1, k):
                if j1 != j2:
                    if t[j1][i] == t[j2][i]:
                        lines_ok[i] = 0
    #return False if lines_ok[i] = 0 for all i
    for i in range(n):
        if lines_ok[i] == 1:
            return True
    return False









#--------------------------------------------------------------------------------------------------------------------------------------------
#   2
#--------------------------------------------------------------------------------------------------------------------------------------------

def digraph_endos_1(G, e, f, v=0):
    n = G.order()
    if v == n:
        if not outdeg_bad(G,f):
            if not_invertible(G,f):
                yield f
    else:
        if v == e:
            yield from digraph_endos_1(G, e, f, v+1)
        else:
            for u in G.vertices(sort=True):
                if u >= f[v]:
                    u_is_bad = False
                    for w in G.neighbors_out(v):
                        if w < v and not G.has_edge(u, f[w]):
                            u_is_bad = True
                            break
                    if not u_is_bad:
                        for w in G.neighbors_in(v):
                            if w < v and not G.has_edge(f[w], u):
                                u_is_bad = True
                                break
                    if not u_is_bad:
                        f[v] = u
                        yield from digraph_endos_1(G, e, f, v+1)
            f[v] = 0

def digraph_endos_2(G, e, f, v=0):
    n = G.order()
    if v == n:
        if not outdeg_bad(G,f):
            if not_invertible(G,f):
                yield f
    else:
        if v == e:
            yield from digraph_endos_2(G, e, f, v+1)
        else:
            for u in G.vertices(sort=True):
                if u >= f[v]:
                    u_is_bad = False
                    for w in G.neighbors_out(v):
                        if w < v and not G.has_edge(u, f[w]):
                            u_is_bad = True
                            break
                    if not u_is_bad:
                        for w in G.neighbors_in(v):
                            if w < v and not G.has_edge(f[w], u):
                                u_is_bad = True
                                break
                    if not u_is_bad:
                        f[v] = u
                        yield from digraph_endos_2(G, e, f, v+1)
            f[v] = 0

def digraph_endos_3(G, e, f, v=0):
    n = G.order()
    if v == n:
        if not outdeg_bad(G,f):
            if not_invertible(G,f):
                yield f
    else:
        if v == e:
            yield from digraph_endos_3(G, e, f, v+1)
        else:
            for u in G.vertices(sort=True):
                if u >= f[v]:
                    u_is_bad = False
                    for w in G.neighbors_out(v):
                        if w < v and not G.has_edge(u, f[w]):
                            u_is_bad = True
                            break
                    if not u_is_bad:
                        for w in G.neighbors_in(v):
                            if w < v and not G.has_edge(f[w], u):
                                u_is_bad = True
                                break
                    if not u_is_bad:
                        f[v] = u
                        yield from digraph_endos_3(G, e, f, v+1)
            f[v] = 0

def check_monoid(d, e, verbatim=False): #given a digraph (with multiedges and loops) checks if it is the cayley digraph of a monoid, given the neutral element e of the monoid. It assumes that the monoid has 3 minimal generators, and tries to find them.
    n = d.order()
    #initialize variables all0 and identity
    all0 = [0 for _ in range(n)]
    identity = [x for x in range(n)]
    #save the underlying graph to use later
    underlying_d = underlying_graph(d)
    #-----------------------------------------------------------
    # Compute the out-neighbors of e, C = {c1,c2,c3}
    #-----------------------------------------------------------
    C = d.neighbors_out(e)
    #-----------------------------------------------------------
    # Pick 1st generator f = lambda_c1
    #-----------------------------------------------------------
    seed_endos_e_to_c1 = all0.copy()
    seed_endos_e_to_c1[e] = C[0]
    endos_e_to_c1 = digraph_endos_1(d.copy(), e, seed_endos_e_to_c1.copy(), 0)
    for f in endos_e_to_c1:
        if verbatim:
            print("f =", f)
        #-----------------------------------------------------------
        # Check that the 1st generator is good so far
        #-----------------------------------------------------------
        #Check outdegree
        if outdeg_bad(d, f):
            if verbatim:
                print("A")
            continue
        #Save the endomorphisms we have for the moment
        s = []
        s.append(identity.copy())
        s.append(f.copy())
        #Check canbepartial
        t1 = closure(s)#list of so-far generated elements (no need for tops, since with one endo+id cannot exceed size)
        if not canbepartial(t1):
            if verbatim:
                print("B")
            continue
        #CHECK IF THE UNDERLING CAY(<c1>,{c1}) IS ISOMORPHIC TO A SUBGRAPH OF OUR GRAPH
        if len(t1) <= n:#breaks if I generate already more morphisms than vertices
            c = [0]#index of generator within t1
            G = underlying_graph(cayley_graph(t1, c))
            if underlying_d.subgraph_search(G) == None:#checks if G is subgraph of H
                if verbatim:
                    print("C")
                continue
        else:
            continue
        #-----------------------------------------------------------
        # Pick 2nd generator g = lambda_c2
        #-----------------------------------------------------------
        seed_endos_e_to_c2 = all0.copy()
        seed_endos_e_to_c2[e] = C[1]
        endos_e_to_c2 = digraph_endos_2(d.copy(), e, seed_endos_e_to_c2.copy(), 0)
        for g in endos_e_to_c2:
            if verbatim:
                print("g =", g)
            #-----------------------------------------------------------
            # Check that the 1st and 2nd generators are good so far
            #-----------------------------------------------------------
            if outdeg_bad(d, g):
                continue
            if (g not in t1):#only take a generator-candidate if it is not yet generated by previous generators
                s = t1.copy()
                s.append(g.copy())
                t2 = closure(s, n)
                bad = False
                for z in t2:
                    if outdeg_bad(d, z):
                        bad = True
                        break
                if bad:
                    continue
                #CHECK IF THE UNDERLING CAY(<c1,c2>,{c1,c2}) IS ISOMORPHIC TO A SUBGRAPH OF OUR GRAPH
                if not canbepartial(t2):
                    continue
                c = [0,len(t1)]
                G = underlying_graph(cayley_graph(t2, c))
                if (underlying_d.subgraph_search(G)==None):
                    continue
                #-----------------------------------------------------------
                # Pick 3rd generator h = lambda_c3
                #-----------------------------------------------------------
                seed_endos_e_to_c3 = all0.copy()
                seed_endos_e_to_c3[e] = C[2]
                endos_e_to_c3 = digraph_endos_3(d.copy(), e, seed_endos_e_to_c3.copy(), 0)
                for h in endos_e_to_c3:
                    if verbatim:
                        print("h =", h)
                    #-----------------------------------------------------------
                    # Check that the 1st, 2nd and 3rd generators are good          (i.e. check if we found the monoid)
                    #-----------------------------------------------------------
                    if outdeg_bad(d, h):
                        continue
                    if (h not in t2):
                        s = t2.copy()
                        s.append(h.copy())
                        t3 = closure(s, n)
                        bad = False
                        for z in t3:
                            if outdeg_bad(d, z):
                                bad = True
                                break
                        if bad:
                            continue
                        if len(t3) == n:
                            if not canbepartial(t3):
                                continue
                            #CHECK IF THE UNDERLING CAY(<c1,c2,c3>,{c1,c2,c3}) IS ISOMORPHIC TO OUR GRAPH
                            m += 1
                            c = [0,len(t1),len(t2)]
                            F = cayley_graph(t3, c)
                            G = underlying_graph(F)
                            if (underlying_d.subgraph_search(G) == None):
                                continue
                            if G.is_isomorphic(underlying_d):
                                print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
                                s = semigroupfromcayley(F)
                                print(m, t3, c)
                                for i in range(F.order()):
                                    print(s[i])
                                print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
                                return True
    return False

def filter_the_ors_G72(): #filter the multiorintations that have a neutral element candidate
    fin = open('G72_multiors.d6', 'r')
    fout = open('G72_multiors_less_new.d6', 'w')
    line = fin.readline()
    cnt = 1
    while line:
        print(cnt, "of 747197622")
        fixed_line = line[1:] #for some reason, nauty gives them all starting with &, which has to be removed
        D = DiGraph(fixed_line, multiedges=True)
        if there_is_e_candidate_G72(D):
            fout.write(fixed_line)
        line = fin.readline()
        cnt += 1
    fin.close()
    fout.close()

def MAIN_approach1(initial_line=1, step=1, verbatim=False): #put loops and check monoid
    import time
    t1 = time.perf_counter()
    #read file with multiorientations of G72
    fin = open('G72_multiors_less_new.d6', 'r')
    line = fin.readline()
    cnt = 0
    cnt_total = 240088032
    real_cnt = 0
    #for each possible multiorientation
    while line:
        cnt += 1
        if cnt % step == initial_line % step:
            real_cnt += 1
            if verbatim:
                print("----------------------------------------------------------------------------------------------------------------------")
                print("----------------------------------------------------------------------------------------------------------------------")
            print("Checking multiorientation", cnt, "of", cnt_total)
            if verbatim:
                print("Multiorientation in format d6:", line)
            D = DiGraph(line,multiedges=True)
            #for each possible addition of loops
            LIST_OF_D_WITH_LOOPS = add_loops(D)
            for d in LIST_OF_D_WITH_LOOPS:
                #for each neutral element candidate
                e_candidates = find_e_candidates_G72_loops(d)
                if verbatim:
                    print("-----------------------------------------------------------")
                    print("New way to add loops. The neutral element candidates are", e_candidates)
                for e in e_candidates:
                    if verbatim:
                        print("e =", e)
                    #check if it is a monoid digraph (using that in this case the monoid has exactly 3 minimal generators)
                    if check_monoid(d, e):
                        return True
                    if verbatim:
                        print("Not a monoid digraph.")
        line = fin.readline()
    fin.close()
    t2 = time.perf_counter()
    print("Number of lines analyzes:", real_cnt)
    print("Computation time:", t2-t1, "seconds")
    return False














#--------------------------------------------------------------------------------------------------------------------------------------------
#   3
#--------------------------------------------------------------------------------------------------------------------------------------------

def digraph_endos_1_INV(G, e, f, v=0):
    n = G.order()
    if v == n:
        if not outdeg_bad(G,f):
            yield f
    else:
        if v == e:
            yield from digraph_endos_1_INV(G, e, f, v+1)
        else:
            for u in G.vertices(sort=True):
                if u >= f[v]:
                    u_is_bad = False
                    for w in G.neighbors_out(v):
                        if w < v and not G.has_edge(u, f[w]):
                            u_is_bad = True
                            break
                    if not u_is_bad:
                        for w in G.neighbors_in(v):
                            if w < v and not G.has_edge(f[w], u):
                                u_is_bad = True
                                break
                    if not u_is_bad:
                        f[v] = u
                        yield from digraph_endos_1_INV(G, e, f, v+1)
            f[v] = 0

def digraph_endos_2_INV(G, e, f, v=0):
    n = G.order()
    if v == n:
        if not outdeg_bad(G,f):
            yield f
    else:
        if v == e:
            yield from digraph_endos_2_INV(G, e, f, v+1)
        else:
            for u in G.vertices(sort=True):
                if u >= f[v]:
                    u_is_bad = False
                    for w in G.neighbors_out(v):
                        if w < v and not G.has_edge(u, f[w]):
                            u_is_bad = True
                            break
                    if not u_is_bad:
                        for w in G.neighbors_in(v):
                            if w < v and not G.has_edge(f[w], u):
                                u_is_bad = True
                                break
                    if not u_is_bad:
                        f[v] = u
                        yield from digraph_endos_2_INV(G, e, f, v+1)
            f[v] = 0

def digraph_endos_3_INV(G, e, f, v=0):
    n = G.order()
    if v == n:
        if not outdeg_bad(G,f):
            yield f
    else:
        if v == e:
            yield from digraph_endos_3_INV(G, e, f, v+1)
        else:
            for u in G.vertices(sort=True):
                if u >= f[v]:
                    u_is_bad = False
                    for w in G.neighbors_out(v):
                        if w < v and not G.has_edge(u, f[w]):
                            u_is_bad = True
                            break
                    if not u_is_bad:
                        for w in G.neighbors_in(v):
                            if w < v and not G.has_edge(f[w], u):
                                u_is_bad = True
                                break
                    if not u_is_bad:
                        f[v] = u
                        yield from digraph_endos_3_INV(G, e, f, v+1)
            f[v] = 0

def check_monoid_INV(d, e, verbatim=False):
    n = d.order()
    #initialize variables all0 and identity
    all0 = [0 for _ in range(n)]
    identity = [x for x in range(n)]
    #save the underlying graph to use later
    underlying_d = underlying_graph(d)
    #-----------------------------------------------------------
    # Compute the out-neighbors of e, C = {c1,c2,c3}
    #-----------------------------------------------------------
    C = d.neighbors_out(e)
    #-----------------------------------------------------------
    # Pick 1st generator f = lambda_c1
    #-----------------------------------------------------------
    seed_endos_e_to_c1 = all0.copy()
    seed_endos_e_to_c1[e] = C[0]
    endos_e_to_c1 = digraph_endos_1_INV(d.copy(), e, seed_endos_e_to_c1.copy(), 0)
    for f in endos_e_to_c1:
        if verbatim:
            print("f =", f)
        #-----------------------------------------------------------
        # Check that the 1st generator is good so far
        #-----------------------------------------------------------
        #Check outdegree
        if outdeg_bad(d, f):
            if verbatim:
                print("A")
            continue
        #Save the endomorphisms we have for the moment
        s = []
        s.append(identity.copy())
        s.append(f.copy())
        #Check canbepartial
        t1 = closure(s)#list of so-far generated elements (no need for tops, since with one endo+id cannot exceed size)
        if not canbepartial(t1):
            if verbatim:
                print("B")
            continue
        #CHECK IF THE UNDERLING CAY(<c1>,{c1}) IS ISOMORPHIC TO A SUBGRAPH OF OUR GRAPH
        if len(t1) <= n:#breaks if I generate already more morphisms than vertices
            c = [0]#index of generator within t1
            G = underlying_graph(cayley_graph(t1, c))
            if underlying_d.subgraph_search(G) == None:#checks if G is subgraph of H
                if verbatim:
                    print("C")
                continue
        else:
            continue
        #-----------------------------------------------------------
        # Pick 2nd generator g = lambda_c2
        #-----------------------------------------------------------
        seed_endos_e_to_c2 = all0.copy()
        seed_endos_e_to_c2[e] = C[1]
        endos_e_to_c2 = digraph_endos_2_INV(d.copy(), e, seed_endos_e_to_c2.copy(), 0)
        for g in endos_e_to_c2:
            if verbatim:
                print("g =", g)
            #-----------------------------------------------------------
            # Check that the 1st and 2nd generators are good so far
            #-----------------------------------------------------------
            if outdeg_bad(d, g):
                continue
            if (g not in t1):#only take a generator-candidate if it is not yet generated by previous generators
                s = t1.copy()
                s.append(g.copy())
                t2 = closure(s, n)
                bad = False
                for z in t2:
                    if outdeg_bad(d, z):
                        bad = True
                        break
                if bad:
                    continue
                #CHECK IF THE UNDERLING CAY(<c1,c2>,{c1,c2}) IS ISOMORPHIC TO A SUBGRAPH OF OUR GRAPH
                if canbepartial(t2):
                    c = [0,len(t1)]
                    G = underlying_graph(cayley_graph(t2, c))
                    if (underlying_d.subgraph_search(G)==None):
                        continue
                    #-----------------------------------------------------------
                    # Pick 3rd generator h = lambda_c3
                    #-----------------------------------------------------------
                    seed_endos_e_to_c3 = all0.copy()
                    seed_endos_e_to_c3[e] = C[2]
                    endos_e_to_c3 = digraph_endos_3_INV(d.copy(), e, seed_endos_e_to_c3.copy(), 0)
                    for h in endos_e_to_c3:
                        if verbatim:
                            print("h =", h)
                        #-----------------------------------------------------------
                        # Check that the 1st, 2nd and 3rd generators are good          (i.e. check if we found the monoid)
                        #-----------------------------------------------------------
                        if outdeg_bad(d, h):
                            continue
                        if (h not in t2):
                            s = t2.copy()
                            s.append(h.copy())
                            t3 = closure(s, n)
                            bad = False
                            for z in t3:
                                if outdeg_bad(d, z):
                                    bad = True
                                    break
                            if bad:
                                continue
                            if len(t3) == n and canbepartial(t3):
                            #CHECK IF THE UNDERLING CAY(<c1,c2,c3>,{c1,c2,c3}) IS ISOMORPHIC TO OUR GRAPH
                                m += 1
                                c = [0,len(t1),len(t2)]
                                F = cayley_graph(t3, c)
                                G = underlying_graph(F)
                                if (underlying_d.subgraph_search(G) == None):
                                    continue
                                if G.is_isomorphic(underlying_d):
                                    print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
                                    s = semigroupfromcayley(F)
                                    endos.add(str(s))
                                    print(m, t3, c)
                                    for i in range(F.order()):
                                        print(s[i])
                                    print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
                                    return True
    return False

def add_loops_INV(d, refl, freevertices, verbatim=False): #add loops symmetrically
    D = d.copy()
    #classify free vertices in three classes: mandatory loops, optional loops and forbidden loops (those that are not mandatory or optional)
    put = [] #mandatory loops
    puttable = [] #optional loops
    for v in freevertices:
        if D.out_degree(v) < 3 and D.out_degree(v) > 1:
            puttable.append(v)
        if D.out_degree(v) == 0:
            put.append(v)
    if verbatim:
        print("put =", put, " puttable =", puttable)
    #add mandatory loops
    for v in put:
        edge = (v, v)
        D.add_edge(v, v)
        refl_edge = (refl(edge[0]), refl(edge[1]))
        if refl_edge != edge:
            D.add_edge(refl_edge)
    #add optional loops
    for S in powerset(puttable):
        if verbatim:
            print("     ", S)
        H = D.copy()
        for v in S:
            edge = (v, v)
            H.add_edge(edge)
            refl_edge = (refl(edge[0]), refl(edge[1]))
            if refl_edge != edge:
                H.add_edge(refl_edge)
        yield H

def partial_orientation(): #e=0 and c=1
    forbidden_edges = [[2,1],[6,0],[8,1],[7,0],[4,3],[4,5],[11,9],[11,13]]
    D = DiGraph(graphs.GeneralizedPetersenGraph(7,2))
    D.delete_edges(forbidden_edges)
    return D.dig6_string()

def partial_orientation_2(): #e=12 and c=10
    forbidden_edges = [[3,10],[5,12],[8,10],[7,12],[4,3],[4,5],[11,9],[11,13]]
    D = DiGraph(graphs.GeneralizedPetersenGraph(7,2))
    D.delete_edges(forbidden_edges)
    return D.dig6_string()

def get_the_ors_G72_INV(): #Create a file G72involution.d6 with all the possible orientations with one invertible element
    fout = open('G72involution.d6', 'w')
    D = DiGraph('MOoIA?OOIA??OIA@?O@G?HGP@AGG?@Q?IO')#this is the partial orientation that we determined in partial_orientation()
    e = 0
    g = D.automorphism_group() #order 2
    refl = g[1] #the involution
    freearcs = [(2, 3), (2, 9), (3, 10), (4, 11), (7, 9), (7, 12)] #they have two antiparallel arcs. we can delete one, delete the other one or leave both
    for FWD in powerset(freearcs): #arcs with at least Forward Direction
        for DD in powerset(FWD): #arcs with Double Direction (it is a subset of FWD)
            H = D.copy()
            for edge in freearcs:
                #the backward arcs (the ones not in FWD)
                if edge not in FWD:
                    H.delete_edge(edge)
                    H.delete_edge(refl(edge[0]), refl(edge[1]))
                #the forward arcs (the ones in FWD and not in DD)
                if edge in FWD and edge not in DD:
                    H.delete_edge(edge[1], edge[0])
                    H.delete_edge(refl(edge[1]), refl(edge[0]))
            #still check if everybody is reachable from e=0
            if everybody_reachable_from_e(H, e):
                fout.write(H.dig6_string()+"\n")
    fout.close()

def get_the_ors_G72_INV_notgen(): #notgen implies not everybody reachable
    fout = open('G72involution_notgen.d6', 'w')
    D = DiGraph('MOoIA?OOIA??OIA@?O@G?HGP@AGG?@Q?IO')#this is the partial orientation that we determined in partial_orientation()
    e = 0
    g = D.automorphism_group() #order 2
    refl = g[1] #the involution
    freearcs = [(2, 3), (2, 9), (3, 10), (4, 11), (7, 9), (7, 12)] #they have two antiparallel arcs. we can delete one, delete the other one or leave both
    for FWD in powerset(freearcs): #arcs with at least Forward Direction
        for DD in powerset(FWD): #arcs with Double Direction (it is a subset of FWD)
            H = D.copy()
            for edge in freearcs:
                #the backward arcs (the ones not in FWD)
                if edge not in FWD:
                    H.delete_edge(edge)
                    H.delete_edge(refl(edge[0]), refl(edge[1]))
                #the forward arcs (the ones in FWD and not in DD)
                if edge in FWD and edge not in DD:
                    H.delete_edge(edge[1], edge[0])
                    H.delete_edge(refl(edge[1]), refl(edge[0]))
            #still check if everybody is reachable from e=0
            if not everybody_reachable_from_e(H, e):
                fout.write(H.dig6_string()+"\n")
    fout.close()

def get_the_ors_G72_INV_2(): #Create a file G72involution.d6 with all the possible orientations with one invertible element
    #import sys
    fout = open('G72involution_2.d6', 'w')
    D = DiGraph('MOoIA@OOI???OI?`?W@@?@GP@AGG?@Q?IO') #this is the partial orientation that we determined in partial_orientation_2()
    e = 12
    g = D.automorphism_group() #order 2
    refl = g[1] #the involution
    freearcs = [(0, 6), (0, 7), (4, 11), (5,6), (6, 13), (7, 9)] #they have two antiparallel arcs. we can delete one, delete the other one or leave both
    for FWD in powerset(freearcs): #arcs with at least Forward Direction
        for DD in powerset(FWD): #arcs with Double Direction (it is a subset of FWD)
            H = D.copy()
            for edge in freearcs:
                #the backward arcs (the ones not in FWD)
                if edge not in FWD:
                    H.delete_edge(edge)
                    H.delete_edge(refl(edge[0]), refl(edge[1]))
                #the forward arcs (the ones in FWD and not in DD)
                if edge in FWD and edge not in DD:
                    H.delete_edge(edge[1], edge[0])
                    H.delete_edge(refl(edge[1]), refl(edge[0]))
            #still check if everybody is reachable from e=0
            if everybody_reachable_from_e(H, e):
                fout.write(H.dig6_string()+"\n")
    fout.close()

def get_the_ors_G72_INV_notgen_2(): #Create a file G72involution.d6 with all the possible orientations with one invertible element
    #import sys
    fout = open('G72involution_notgen_2.d6', 'w')
    D = DiGraph('MOoIA@OOI???OI?`?W@@?@GP@AGG?@Q?IO')#this is the partial orientation that we determined in partial_orientation_2()
    e = 12
    g = D.automorphism_group() #order 2
    refl = g[1] #the involution
    freearcs = [(0, 6), (0, 7), (4, 11), (5,6), (6, 13), (7, 9)] #they have two antiparallel arcs. we can delete one, delete the other one or leave both
    for FWD in powerset(freearcs): #arcs with at least Forward Direction
        for DD in powerset(FWD): #arcs with Double Direction (it is a subset of FWD)
            H = D.copy()
            for edge in freearcs:
                #the backward arcs (the ones not in FWD)
                if edge not in FWD:
                    H.delete_edge(edge)
                    H.delete_edge(refl(edge[0]), refl(edge[1]))
                #the forward arcs (the ones in FWD and not in DD)
                if edge in FWD and edge not in DD:
                    H.delete_edge(edge[1], edge[0])
                    H.delete_edge(refl(edge[1]), refl(edge[0]))
            #still check if everybody is reachable from e=0
            if not everybody_reachable_from_e(H, e):
                fout.write(H.dig6_string()+"\n")
    fout.close()

def MAIN_approach1_INV(verbatim=False): #put loops symmetrically and check monoid
    import time
    t1 = time.perf_counter()
    D = DiGraph('MOoIA?OOIA??OIA@?O@G?HGP@AGG?@Q?IO')#this is the partial orientation that we determined in partial_orientation()
    e = 0
    g = D.automorphism_group() #order 2
    refl = g[1] #the involution
    freevertices = [4, 5, 6, 7, 11, 12, 13] #those that can have loops (and then per symmetry determine the rest)
    fin = open('G72involution.d6', 'r')
    number_of_lines = count_lines('G72involution.d6')
    fout = open('AA_output_MAIN_approach1_INV', 'w')
    lines = fin.readlines()
    counter = 0
    counter_2 = 0
    for l in lines:
        counter += 1
        print("Checking line", counter, "of", number_of_lines)
        D = DiGraph(l, multiedges=True, loops=True)
        #put loops symmetrically
        for H in add_loops_INV(D, refl, freevertices):
            if len(H.loops()) > 0: #since G72 is a core, we know that there have to be loops when non-group semigroup graph
                fout.write(str(edges_list(H))+"\n")
                #check if is monoid
                counter_2 += 1
                if check_monoid_INV(H, e):
                    return True
    fin.close()
    print("Number of looped digraphs analized:", counter_2)
    t2 = time.perf_counter()
    print("Computation time:", t2-t1, "seconds")
    return False

def MAIN_approach1_INV_2(verbatim=False): #put loops symmetrically and check monoid
    import time
    t1 = time.perf_counter()
    D = DiGraph('MOoIA@OOI???OI?`?W@@?@GP@AGG?@Q?IO') #this is the partial orientation that we determined in partial_orientation_2()
    e = 12
    g = D.automorphism_group() #order 2
    refl = g[1] #the involution
    freevertices = [0, 4, 5, 6, 7, 11, 13] #those that can have loops (and then per symmetry determine the rest)
    fin = open('G72involution_2.d6', 'r')
    number_of_lines = count_lines('G72involution_2.d6')
    fout = open('AA_output_MAIN_approach1_INV_2', 'w')
    lines = fin.readlines()
    counter = 0
    counter_2 = 0
    for l in lines:
        counter += 1
        print("Checking line", counter, "of", number_of_lines)
        D = DiGraph(l, multiedges=True, loops=True)
        #put loops symmetrically
        for H in add_loops_INV(D, refl, freevertices):
            if len(H.loops()) > 0: #since G72 is a core, we know that there have to be loops when non-group semigroup graph
                fout.write(str(edges_list(H))+"\n")
                #check if is monoid
                counter_2 += 1
                if check_monoid_INV(H, e):
                    return True
    fin.close()
    print("Number of looped digraphs analized:", counter_2)
    t2 = time.perf_counter()
    print("Computation time:", t2-t1, "seconds")
    return False



