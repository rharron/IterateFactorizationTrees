#*****************************************************************************
#       Copyright (C) 2016 Robert Harron <robert.harron@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

import sys

def compute_tree(f, p, level, return_tree=False, digraph=False, show_text=False, return_verts=False):
    r"""
    This function computes the iterated factorization tree of ``f`` modulo ``p`` up to level ``level``
    as in Section 3 of Nigel Boston and Rafe Jones's article Settled polynomials over finite fields.
    As such, it returns a tree (and possibly that tree's plot and list of vertices) whose vertices are
    irreducible polynomials `h\in\FF_p[x]` that divide `f^n` for some `0\leq n\leq \mathrm{level}`, with
    an edge connecting `h_1` to `h_2` when `h_2\mid h_1\circ f`. The vertices are labelled as follows.
    Let `\gamma` be the critical point of `f` and let `f(\gamma)`, `f^2(\gamma)`, ..., `f^r(\gamma)` the
    elements of its forward orbit (in that order). The vertex corresponding to `h` is labelled by a string
    of length `r` of n's and s's encoding whether `h(f^k(\gamma))` is a square or not (call this its symbol)
    To this label is appended n_i_j, where n is the level of the tree in which `h` appears, i indicates `h`
    divides `h_i\circ f` where `h_i` is the ith factor at the previous level, and j indicates `h` is the jth
    factor of `h_i\circ f`, ordered lexicographically by its symbol (i and j are both zero-based indices).
    The root of the tree generated is just a dummy root labelled root, though I guess we could assign it the
    symbol of the polynomial x.
    
    INPUT::
    
    -``f`` : a quadratic polynomial over ZZ or FF_p.
    -``p`` : a prime (odd?).
    -``return_tree`` : a poorly-named boolean variable you should set to True if you want the *plot*
    of the tree to be returned by this function.
    -``digraph`` : a boolean you should set to True if you want the tree to be directed.
    -``show_text`` : a boolean you should set to True if you want ``p``, as well as its congruence classes
    mod some powers of 2 displayed on the plot.
    -``return_verts : a boolean you should set to True if you want the list of vertices of the tree returned.
    
    OUTPUT::
    
    Possible outputs are (``G``, ``PPP``, ``verts``), (``G``, ``PPP``), (``G``, ``verts``), or simply ``G``,
    depending on the above booleans. Where:
    
    -``G`` : a graph (or directed graph) whose vertices are labelled as described above.
    -``PPP``` : a plot of the tree generated. The vertices are coloured with the nnn...n coloured black and the
    remaining symbols rainbow coloured red to indigo according to their lexicographic ordering.
    -``verts`` : The reason you might want this list returned is that it gives a convenient way to obtain the
    vertices ordered as they are displayed on the plot. ``verts`` is a list of lists such that ``verts[n]`` is
    the ordered list of vertix labels at level ``n+1``.
    
    NOTES::
    
    -The size of the vertices may need to be modified if you use say > 15 or 16 levels. If you do 24 levels, this
    is taken care of in the code (though in that case the text, if displayed, will look ridiculous!).
    -The tree will stop if a level is reached where all vertices are black and correspond to factors of degree
    at least 2; in this case, the tree is just unsplit black vertices all the way down after that.
    """
    alphabet = ['n', 's']
    N = level+1
    #col = {'nn' : 'B', 'ns' : 'u', 'sn' : 'P', 'ss' : 'G'}
    fn = f.change_ring(Zmod(p))
    c0 = fn.derivative().roots()[0][0]
    cs = []
    found = False
    c = c0
    while not found:
        c = fn(c)
        found = (c in cs)
        if not found:
            cs.append(c)
    L = len(cs)
    symbols = []
    for m in mrange([len(alphabet)]*L):
        s = [alphabet[i] for i in m]
        s = ''.join(s)
        symbols.append(s)
    colours = ['#000000'] + rainbow(2^L - 1)
    #coltoplot = {'nn' : '#000000', 'ns' : '#0000ff', 'sn': '#ff0000', 'ss' : '#00ff00'}
    coltoplot = dict(zip(symbols, colours))
    #print coltoplot
    emptylists = []
    for cols in colours:
        emptylists.append([cols, []])
    #plotcolors = {'#000000' : [], '#0000ff' : [], '#ff0000' : [], '#00ff00' : []}
    plotcolors = dict(emptylists)
    #print plotcolors
    fis = [fact for fact, _ in fn.factor()]
    #fis
    tags = [['s' if fii(c).is_square() else 'n' for c in cs]for fii in fis]
    #tags
    j = 0
    for i in range(len(tags)):
        tag = ''
        for stri in tags[i]:
            tag += stri
            #print tag
        tags[i] = tag
    if len(tags) > 1 and tags[1] < tags[0]:
        tags.reverse()
        fis.reverse()
    for i in range(len(tags)):
        tags[i] = tag + '1_0_%s'%(i)
    #print tags
    #tags
    #tags
    #assert(False)
    if digraph:
        G = DiGraph()
    else:
        G = Graph()
    G.add_vertex('root')
    verts = []
    #G.add_vertex('u1_0_0')
    prevtags = tags#['u1_0_0']
    verts.append(prevtags)
    edges = [('root', tag) for tag in prevtags]
    plotcolors['#ffffff'] = ['root']
    for v in prevtags:
        plotcolors[coltoplot[v[0:L]]].append(v)
    prevfis = fis
    for n in range(2,N):
        #print n
        sys.stdout.flush()
        #print "n =", n
        #print prevfis
        #print prevtags
        #print
        #Check if tree has stabilized
        allB = True
        for i in range(len(prevfis)):
            if (type(prevfis[i]) == type('') or (prevtags[i][0:L] == symbols[0] and prevfis[i].degree() > 1)):
                continue
            allB = False
            break
        if allB:
            #print "All black (and non degree 1). Stop."
            #print prevfis
            break
        #print
        #print prevtags
        #print n
        #print "!", prevfis
        
        #Determine this level
        fis = [[symbols[0]] if (type(prevfis[i]) == type('') or (prevtags[i][0:L] == symbols[0] and prevfis[i].degree() > 1)) else [fact for fact, _ in fis[i](f).factor()] for i in range(len(fis))]
        tags = [[['s' if fii(c).is_square() else 'n' for c in cs] if fii != symbols[0] else symbols[0] for fii in fi] for fi in fis]
        for i in range(len(tags)):
            for j in range(len(tags[i])):
                tag = ''
                for stri in tags[i][j]:
                    tag += stri
                tags[i][j] = tag
            if len(tags[i]) == 1:
                continue
            #if tags[i][1] == symbols[0] and tags[i][0] != symbols[0]:
            if tags[i][1] < tags[i][0]:
                temp = tags[i][1]
                tags[i][1] = tags[i][0]
                tags[i][0] = temp
                temp = fis[i][0]
                fis[i][0] = fis[i][1]
                fis[i][1] = temp
        #print ".", tags
        #print fis
        #print n, tags
        vertstoadd = []
        edgestoadd = []
        for i in range(len(tags)):
            for j in range(len(tags[i])):
                newname = tags[i][j] + "%s_%s_%s"%(n,i,j)
                #G.add_vertex(newname)
                vertstoadd.append(newname)
                plotcolors[coltoplot[tags[i][j]]].append(newname)
                #G.add_edge((prevtags[i], newname))
                edgestoadd.append((prevtags[i], newname))
        #print vertstoadd
        #vertstoadd.sort(key=sortcolorkey)
        #print vertstoadd
        #for v in vertstoadd:
        #    G.add_vertex(v)
        #for e in edgestoadd:
        #    G.add_edge(e)
        verts.append(vertstoadd)
        edges += edgestoadd
        if n == N-1:
            break
        tags2 = []
        for i in range(len(tags)):
            for j in range(len(tags[i])):
                tags2.append(tags[i][j] + "%s_%s_%s"%(n,i,j))
        #for tag in tags:
        #    tags2 += tag
        prevtags = tags2
        #print prevtags
        #print n
        fis2 = []
        for fi in fis:
            fis2 += fi
        fis = fis2
        prevfis = fis2
        #print fis
        #print prevtags
        #print
    #verts
    #edges
    #pos_dict = {}
    #n = 1.0
    #for vs in verts:
    #    #j = 0.0
    #    for v in vs:
    #        G.add_vertex(v)
    #        #pos_dict[v] = (j, -n)
    #        #j += 1
    #    #n += 1
    #for e in edges:
    #    G.add_edge(e)
    tree_plotter(verts, edges, G)
    #PPP = G.plot(layout='tree', vertex_colors=plotcolors, vertex_labels=False, figsize=[7*len(verts), 7*len(verts)], tree_root='root', save_pos=True)
    if return_tree:
        if level != 24:
            PPP = G.plot(vertex_colors=plotcolors, vertex_labels=False, figsize=[7*len(verts), 7*len(verts)])
            if show_text:
                PPP = PPP + text("p = %s\n%s\n\np mod 2^i (i=3, ..., 7)"%(p, [p % 2^i for i in range(3,8)]), (0,0), axes=False, horizontal_alignment='left', fontsize=64)
        else:
            PPP = G.plot(vertex_colors=plotcolors, vertex_labels=False, figsize=[7*len(verts), 7*len(verts)], vertex_size=4)
    #PPP.show()
    #PPP = G.plot(layout='tree', vertex_colors=plotcolors, vertex_labels=False, vertex_size=4, figsize=[200,200]) #you may want to change the vertex_size and figsize if you change the number of levels computed
    #PPP.save('AIM_arith_dyn/pdfs/p%s_level%s.pdf'%(p, len(verts)))
    #print p, len(verts), 'done'
    sys.stdout.flush()
    #print verts
    if return_tree:
        if return_verts:
            return G, PPP, verts
        return G, PPP
    if return_verts:
        return G, verts
    return G

def average(a, b):
    return (a+b)/2

def tree_plotter(verts, edges, G):
    r"""
    A utitlity function for determining the positions of the vertices in the plot
    of a tree.
    
    INPUT:
    
    -``verts`` : a list of lists where ``verts[n]`` is the labels of the ``n+1``th level of the tree,
    ordered left to right.
    -``edges`` : a list of edges
    -``G`` : a ``Graph`` object.
    
    This function doesn't actually output anything. It modifies ``G`` in place. It adds all the
    vertices in ``verts`` to ``G``, as well as all of the edges in ``edges``. It also determines
    postions for the vertices and adds the position dictionary created to ``G``.
    """
    n = ZZ(len(verts))
    m = len(verts[n-1])
    #print n
    #type(ZZ(n))
    #for j in srange(m):
    #    print type(j)
    positions = [[(j, -n) for j in srange(m)]]
    #print "a"
    for r in srange(n - 1, 0, -1):
        newpositions = []
        j = 0 #on level r+1
        #i = 0 #on level r
        vs = verts[r]
        while j < len(vs):
            v0 = vs[j]
            if j + 1 >= len(vs) or vs[j+1][-1] == '0': #has no sibling
                newpositions.append((positions[0][j][0], -r))
                j += 1
                continue
            #else has a sibling
            newpositions.append((average(positions[0][j][0], positions[0][j+1][0]), -r))
            j += 2
        newpositions = [newpositions]
        positions = newpositions + positions
    pos_dict = []
    for i in range(len(verts)):
        for j in range(len(verts[i])):
            G.add_vertex(verts[i][j])
            pos_dict.append([verts[i][j], positions[i][j]])
    pos_dict = dict(pos_dict)
    if len(verts[0]) == 1:
        pos_dict['root'] = (pos_dict[verts[0][0]][0], 0)
    else:
        pos_dict['root'] = (average(pos_dict[verts[0][0]][0], pos_dict[verts[0][1]][0]), 0)
    G.set_pos(pos_dict)
    for e in edges:
        G.add_edge(e)
    return
    #PPP = G.plot(vertex_colors=plotcolors, vertex_labels=False, figsize=[7*len(verts), 7*len(verts)], tree_root='root', save_pos=True)

def compute_tree_verts(f, p, level):
    r"""
    This function is similar to ``compute_tree`` above, but does not build a graph. Instead,
    it just builds a list of vertex labels. Its output is ``verts``, a list of lists such that
    ``verts[n]`` is the list of vertices at the ``n+1``th level. Unlike ``compute_tree``, the
    labels of the vertices here are only the 'symbol' of the vertex, not the auxilary n_i_j.
    """
    alphabet = ['n', 's']
    N = level+1
    #col = {'nn' : 'B', 'ns' : 'u', 'sn' : 'P', 'ss' : 'G'}
    fn = f.change_ring(Zmod(p))
    c0 = fn.derivative().roots()[0][0]
    cs = []
    found = False
    c = c0
    while not found:
        c = fn(c)
        found = (c in cs)
        if not found:
            cs.append(c)
    L = len(cs)
    symbols = []
    for m in mrange([len(alphabet)]*L):
        s = [alphabet[i] for i in m]
        s = ''.join(s)
        symbols.append(s)
    fis = [fact for fact, _ in fn.factor()]
    #fis
    tags = [['s' if fii(c).is_square() else 'n' for c in cs]for fii in fis]
    #tags
    j = 0
    for i in range(len(tags)):
        tag = ''
        for stri in tags[i]:
            tag += stri
            #print tag
        tags[i] = tag
    verts = []
    #G.add_vertex('u1_0_0')
    prevtags = tags#['u1_0_0']
    verts.append(prevtags)
    prevfis = fis
    #print 'verts =', verts
    for n in range(2,N):
        #Check if tree has stabilized
        allB = True
        for i in range(len(prevfis)):
            if (type(prevfis[i]) == type('') or (prevtags[i][0:L] == symbols[0] and prevfis[i].degree() > 1)):
                continue
            allB = False
            break
        if allB:
            #print "All black (and non degree 1). Stop."
            #print prevfis
            break
        #print
        #print prevtags
        #print n
        #print "!", prevfis
        
        #Determine this level
        fis = [[symbols[0]] if (type(prevfis[i]) == type('') or (prevtags[i][0:L] == symbols[0] and prevfis[i].degree() > 1)) else [fact for fact, _ in fis[i](f).factor()] for i in range(len(fis))]
        tags = [[['s' if fii(c).is_square() else 'n' for c in cs] if fii != symbols[0] else symbols[0] for fii in fi] for fi in fis]
        for i in range(len(tags)):
            for j in range(len(tags[i])):
                tag = ''
                for stri in tags[i][j]:
                    tag += stri
                tags[i][j] = tag
            if len(tags[i]) == 1:
                continue
        verts.append(flatten(tags))
        if n == N-1:
            break
        tags2 = []
        for i in range(len(tags)):
            for j in range(len(tags[i])):
                tags2.append(tags[i][j])# + "%s_%s_%s"%(n,i,j))
        #for tag in tags:
        #    tags2 += tag
        prevtags = tags2
        #print prevtags
        #print n
        fis2 = []
        for fi in fis:
            fis2 += fi
        fis = fis2
        prevfis = fis2
    return verts

#This is the transition information for the Markov process for (x+1)^2-2
xp1sm2_markov_dict = {'nn' : [['nn']], 'ns' : [['sn']], 'sn' : [['nn', 'sn'], ['ns', 'ss']], 'ss' : [['nn', 'nn'], ['ns', 'ns'], ['sn', 'sn'], ['ss', 'ss']]}

def markov_tree_generator(markov_dict, level, return_tree=False, verbose=False, return_verts=False):
    r"""
    This function creates a tree like that outputted by ``compute_tree``, but it's a fake (plastic?) tree
    randomly-generated by the inputted Markov process information.
    
    The format of markov_dict is as follows. It is a dictionary whose keys consist of all of the possible
    states, i.e. all 'symbols' as described above. The value at a given symbol is a list of lists giving the
    possible transitions, assumed to be equally probable.
    """
    symbols = markov_dict.keys()
    symbols.sort()
    L = len(symbols[0])
    colours = ['#000000'] + rainbow(2^L - 1)
    coltoplot = dict(zip(symbols, colours))
    emptylists = []
    for cols in colours:
        emptylists.append([cols, []])
    plotcolors = dict(emptylists)
    G = Graph()
    G.add_vertex('root')
    verts = [['ns1_0_0']]
    edges = [('root', tag) for tag in verts[-1]]
    plotcolors['#ffffff'] = ['root']
    for v in verts[-1]:
        plotcolors[coltoplot[v[0:L]]].append(v)
    N = level+1
    for n in range(2, N):
        if verbose:
            print n
        sys.stdout.flush()
        vertstoadd = []
        edgestoadd = []
        for i in range(len(verts[-1])):
            v = verts[-1][i]
            possibles = markov_dict[v[:L]]
            pL = len(possibles)
            if pL == 1:
                newvs = possibles[0]
                #print "pL1", n, newvs
                #print markov_dict
            else:
                newvs = copy(possibles[ZZ.random_element(pL)])
            for j in range(len(newvs)):
                newvs[j] += '%s_%s_%s'%(n, i, j)
                vertstoadd.append(newvs[j])
                edgestoadd.append([v, newvs[j]])
                plotcolors[coltoplot[newvs[j][0:L]]].append(newvs[j])
        verts.append(vertstoadd)
        edges += edgestoadd
        if verbose:
            print n, 'done'
        sys.stdout.flush()
    #print verts
    #print plotcolors
    #print edges
    tree_plotter(verts, edges, G)
    if return_tree:
        if level != 24:
            PPP = G.plot(vertex_colors=plotcolors, vertex_labels=False, figsize=[7*len(verts), 7*len(verts)])
        else:
            PPP = G.plot(vertex_colors=plotcolors, vertex_labels=False, figsize=[7*len(verts), 7*len(verts)], vertex_size=4)
    if return_tree:
        return G, PPP
    if return_verts:
        return G, verts
    return G

def markov_tree_verts(markov_dict, level):
    r"""
    This functions is to ``markov_tree_generator`` what ``compute_tree_verts`` is to
    ``compute_tree``.
    """
    symbols = markov_dict.keys()
    symbols.sort()
    L = len(symbols[0])
    #colours = ['#000000'] + rainbow(2^L - 1)
    #coltoplot = dict(zip(symbols, colours))
    #emptylists = []
    #for cols in colours:
    #    emptylists.append([cols, []])
    #plotcolors = dict(emptylists)
    #G = Graph()
    #G.add_vertex('root')
    verts = [['ns']]
    #edges = [('root', tag) for tag in verts[-1]]
    #plotcolors['#ffffff'] = ['root']
    #for v in verts[-1]:
    #    plotcolors[coltoplot[v[0:L]]].append(v)
    N = level+1
    for n in range(2, N):
        #if verbose:
        #    print n
        #sys.stdout.flush()
        vertstoadd = []
        #edgestoadd = []
        for i in range(len(verts[-1])):
            v = verts[-1][i]
            possibles = markov_dict[v[:L]]
            pL = len(possibles)
            if pL == 1:
                newvs = possibles[0]
                #print "pL1", n, newvs
                #print markov_dict
            else:
                newvs = copy(possibles[ZZ.random_element(pL)])
            for j in range(len(newvs)):
                #newvs[j] += '%s_%s_%s'%(n, i, j)
                vertstoadd.append(newvs[j])
                #edgestoadd.append([v, newvs[j]])
                #plotcolors[coltoplot[newvs[j][0:L]]].append(newvs[j])
        verts.append(vertstoadd)
        #edges += edgestoadd
        #if verbose:
        #    print n, 'done'
        #sys.stdout.flush()
    #print verts
    #print plotcolors
    #print edges
    #tree_plotter(verts, edges, G)
    #if return_tree:
    #    if level != 24:
    #        PPP = G.plot(vertex_colors=plotcolors, vertex_labels=False, figsize=[7*len(verts), 7*len(verts)])
    #    else:
    #        PPP = G.plot(vertex_colors=plotcolors, vertex_labels=False, figsize=[7*len(verts), 7*len(verts)], vertex_size=4)
    #if return_tree:
    #    return G, PPP
    #if return_verts:
    #    return G, verts
    #return G
    return verts
