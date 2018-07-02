import sets
import Queue

#helper function that expands a path that goes though a blossom 
def expand(G,G_prime,P_prime):  
    #note that len(G) is the index of the blossom in the graph G_prime
    #since we simply appended the blossom onto G to make G_prime
    #therefore if index len(G) is not in the path, then neither is the blossom
    #and we can return the path without worrying about expanding
    if not len(G) in P_prime:  
        return P_prime         
    else:
        #If the blossom is at an even position in the path 
        #then the stem of the blossom is to the lower part of the augmenting path
        #and the higher part of the cycle connects to a non-stem vertex (vice versa for odd)
        cycle = G_prime[-1]['cycle']
        position = P_prime.index(len(G))
        if position%2 == 0:
            reverse_middle = True #when we insert the expanded blossom into the path the direction is important
            non_stem_neighbor = P_prime[position+1]
        else:
            reverse_middle = False
            non_stem_neighbor = P_prime[position-1]
            
        #if both halves of the path happen to connect to the stem vertex of the blossom
        #then we just swap out that vertex for the blossom in the path and return the path
        if cycle[0] in G[non_stem_neighbor]['adj']:
            P_prime[position] = cycle[0]
            return P_prime
            
        #otherwise, replace the blossom with the path segment of the cycle of the blossom
        else:
            first_half = P_prime[:position]
            second_half = P_prime[position+1:]
            for i in range(len(cycle)):
                #find which vertex in the cycle connects to the path
                if non_stem_neighbor in G[cycle[i]]['adj']:
                    start = i
                    break
                
            middle = []            
            #when we connect to the blossom we need to know which direction to go
            #we must go in the direction of the paired vertex
            if G[cycle[start]]['partner'] == cycle[start-1]: 
                for i in range(start,-1,-1):
                    middle.append(cycle[i])
            else:
                for i in range(start, len(cycle)):
                    middle.append(cycle[i])
                    
            P = first_half 
            if reverse_middle:
                middle.reverse()
            P = P + middle
            P = P + second_half
            return P
    return []
 
#helper function that contracts a graph when a blossom is found   
def contract(G,v,w):
    #start by finding the path to the stem from each vertex (LCA algorithm)
    path_to_stem_v = [v] 
    path_to_stem_w = [w]
    while G[v]['parent'] != -1:
        path_to_stem_v.append(G[v]['parent'])
        v = G[v]['parent']
    while G[w]['parent'] != -1:
        path_to_stem_w.append(G[w]['parent'])
        w = G[w]['parent']
    while len(path_to_stem_v)>0 and len(path_to_stem_w)>0:
        if path_to_stem_v[-1] == path_to_stem_w[-1]:
            lowest_common_ancestor = path_to_stem_v[-1]
            path_to_stem_v = path_to_stem_v[:-1]
            path_to_stem_w = path_to_stem_w[:-1]
        else:
            break
        
    #make the cycle that is contracted into a blossom (starts and ends with the stem vertex)
    cycle = [lowest_common_ancestor] 
    for i in reversed(path_to_stem_w):
        cycle.append(i)
    cycle = cycle + path_to_stem_v + [lowest_common_ancestor] 
    blossom_verteces = sets.Set(cycle)
    
    #make the blossom vertex to add to the graph after changing all the verteces
    #a blossom vertex, unlike a regular one, will have a 'cycle' key to remember what its made of
    blossom_vertex = { 'adj':[], 'partner':-1, 'blossom':-1, 'cycle':cycle }
    
    #rebuild G, updating partners and adjacency lists as appropriate now that a blossom is replacing the verteces of it's cycle
    contracted_G = [] 
    for i in range(len(G)):
        vertex = {} 
        if G[i]['blossom'] != -1: #if a vertex is already part of a different blossom, mark it as such and move on 
            vertex['blossom'] = G[i]['blossom'] 
        else:
            if i in blossom_verteces: #if a vertex is a part of the blossom being made, mark it as such and move on
                vertex['blossom'] = len(G) #len(G) is the index of the new blossom vertex (since we will be appending it to the new graph)
            else:
                vertex['blossom'] = -1   
                if G[i]['partner'] in blossom_verteces: #if a vertex was partners with a vertex in the blossom
                    vertex['partner'] = len(G)          #it is now partners with the blossom
                    blossom_vertex['partner'] = i
                else:
                    vertex['partner'] = G[i]['partner'] #otherwise it keeps its partner
                    
                #here we rebuild the adjency list for the verteces
                vertex['adj'] = []
                adjacent_to_blossom = False 
                for j in G[i]['adj']:
                    if j in blossom_verteces:
                        adjacent_to_blossom = True #make a note if the vertex was adjacent to any of the blossom verteces
                    else:
                        vertex['adj'].append(j) #keep all non-blossom neighbors
                if adjacent_to_blossom:
                    vertex['adj'].append(len(G)) 
                    blossom_vertex['adj'].append(i)
              
        contracted_G.append(vertex) 
    contracted_G.append(blossom_vertex)
    return contracted_G
            
#the algorithm takes an adjacency list and returns a maximum matching in the form of a list of partners as tuples
def max_matching(adj):
    def invert(aug_path,G): 
        for i in range(len(aug_path)//2):
            G[aug_path[2*i]]['partner'] = aug_path[2*i+1]
            G[aug_path[2*i+1]]['partner'] = aug_path[2*i]
    
    def find_aug_path(G):
        def add_match_to_tree(v,w,w_partner):
            G[w]['parent'] = v
            G[w_partner]['parent'] = w
            G[w]['root'] = G[v]['root']
            G[w_partner]['root'] = G[v]['root']
            G[w]['distance'] = G[v]['distance'] + 1
            G[w_partner]['distance'] = G[v]['distance'] + 2
            
        #the 'expand' and 'contract' functions could also be nested here, 
        #since they are only used by 'find_aug_path' but they are quite long
        
        forest = []
        for i in range(len(G)):
            if G[i]['blossom'] == -1: #we only consider verteces not inside a blossom
                G[i]['parent'] = -1   
                if G[i]['partner'] == -1: #each unpaired vertex is the root of a bfs tree in the forest
                    forest.append(i)
                    G[i]['distance'] = 0
                    G[i]['root'] = i
                else:                     #each paired vertex is not part of a bfs tree yet
                    G[i]['distance'] = len(G) + 1 #infinity
                    G[i]['root'] = -1
        for i in forest:
            q = Queue.Queue()
            q.put(i)
            while not q.empty():
                v = q.get()
                #    The first loop scans over all neighbors checking only for unmatched verteces 
                #    Note that the wikipedia page does not include this in any pseudocode. It is not 
                #necessary, but without this loop, if a blossom is found before an unmatched vertex,
                #then the algorithm will contract the graph and recurse which can be time consuming
                for w in G[v]['adj']: 
                    if G[w]['partner'] == -1:
                        P = [v,w]
                        while(G[v]['parent']!=-1):
                            P.insert(0,G[v]['parent'])
                            v = G[v]['parent']
                        while(G[w]['parent']!=-1):
                            P.append(G[w]['parent'])
                            w = G[w]['parent']
                        return P
                for w in G[v]['adj']:
                    if G[w]['partner'] != -1 and G[w]['root'] == -1:
                        add_match_to_tree(v,w,G[w]['partner'])
                        q.put(G[w]['partner'])
                    elif G[w]['distance']%2 == 1:
                        pass
                    elif G[w]['distance']%2 == 0 and G[w]['root'] == G[v]['root']:
                        G_prime = contract(G,v,w)
                        P_prime = find_aug_path(G_prime)
                        P = expand(G,G_prime,P_prime)
                        return P
                    else:
                        P = [v,w]
                        while G[v]['parent']!=-1:
                            P.insert(0,G[v]['parent'])
                            v = G[v]['parent']
                        while G[w]['parent']!=-1:
                            P.append(G[w]['parent'])
                            w = G[w]['parent']
                        return P
        return []
    
    #***********algorithm starts here by making a graph from the adjacency list****************
    G = []
    for i in range(len(adj)):
        vertex = {
        'partner':-1, #starting out none of the verteces are partnered
        'blossom':-1, #also none of them are part of a blossom
        'adj':[] }
        for j in adj[i]:
            vertex['adj'].append(j)
        G.append(vertex)
    #these following 6 lines are the core of many matching algorithms, the strategy of finding the paths is what changes
    #If you find an augmenting path, invert it and look for another augmenting path
    #If you can't find one, the graph is at a maximum matching and the algorithm concludes
    while True:
        aug_path = find_aug_path(G)
        if len(aug_path) == 0:
            break
        else:
            invert(aug_path,G)
            
    matching = [];
    for i in range(len(G)):
        if i < G[i]['partner']:
            matching.append((i,G[i]['partner']))
    return matching                         
        
#some examples:        
        
test_adj_0 = [
[1,2,3],
[0,2],
[0,1],
[0]]

test_adj_1 = [
[3,4],
[3],
[3],
[0,1,2],
[0,5],
[4]]
                  
print(max_matching(test_adj_0))
print(max_matching(test_adj_1)) 