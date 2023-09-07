Read("ChordlessCycles.g");

# Algorithm from Enami
# Computes for a given 3-connected cubic planar symmetric digraph simplicial embeddings
# in projective plane, torus, klein bottle

# Computes the facial cycles of a digraph such that they are oriented in the same direction
FacialCycles:=function(digraph)
    local cycles, edgesOfCycles, c, edgesOfCycle, i, edges, restCyles, cycle, edge, remove, p, rev, contained;

    cycles:=List(AllChordlessCycles(digraph),c->AdjacencyMatrixFromList(c,DigraphNrVertices(digraph)));
    cycles:=Filtered(cycles,c->IsNonSeparating(digraph,c));
    cycles:=List(cycles,c->NodesOfCycle(c));
    
    # Computes the edges for cycles in the direction they are stored.
    edgesOfCycles:=[];
    for c in cycles do
        edgesOfCycle:=[];
        for i in [1..Length(c)] do
            if i=Length(c) then
                Add(edgesOfCycle,[c[i],c[1]]);
            else
                Add(edgesOfCycle,[c[i],c[i+1]]);
            fi;
        od;
        Add(edgesOfCycles,edgesOfCycle);
    od;

    # The edges for which we fixed the direction. 
    # Each arc has to be traversed one time in each direction.
    edges:=[];

    restCyles:=ShallowCopy(cycles);
    while restCyles<>[] do

        # Choose a cycle for which the direction depends on the cycles we fixed already.
        cycle:=0;
        for c in restCyles do
            for edge in edgesOfCycles[Position(cycles,c)] do
                if (edge in edges or Reversed(edge) in edges) and cycle=0 then
                    cycle:=c;
                fi;
            od;
        od;
        if cycle=0 then
            cycle:=restCyles[1];
        fi;
        
        remove:=[];
        for c in restCyles do
            p:=Position(cycles,c);

            # Stores if we have to reverse the direction of this cycle.
            rev:=false;
            # Stores if the direction of an edge of the cycle is already fixed.
            contained:=false;
            for edge in edgesOfCycles[p] do
                # The edge is already used in this direction.
                if edge in edges then #and First(edgesOfCycles[p])=edge then
                    rev:=true;
                    contained:=true;
                # For this edge we can stay in this orientation but we had an edge before 
                # for which we had to reverse the direction of the cycle.
                elif Reversed(edge) in edges and rev then
                    return fail;
                # The reversed edge is used so we do not have to reverse the direction.
                elif Reversed(edge) in edges then   
                    contained:=true;
                fi;
            od;

            # If an edge of the cycle is contained the direction
            # of this cycle is already fixed.
            if contained then
                Add(remove,c);
                if rev then
                    cycles[p]:=Reversed(cycles[p]);
                fi;
            fi;
        od;

        # The direction of this cycle is not fixed by the cycles we considered yet.
        if not cycle in remove then
            Add(remove,cycle);
        fi;

        # For all cycles in remove is the direction fixed and consistent.
        for c in remove do
            Remove(restCyles,Position(restCyles,c));
            if c in cycles then
                Append(edges,edgesOfCycles[Position(cycles,c)]);
            else # If we have reversed the cycle.
                Append(edges,List(edgesOfCycles[Position(cycles,Reversed(c))],p->Reversed(p)));
            fi;
        od;
    od;
    return cycles;
end;

# Compute the rotation system for a given 3-connected cubic planar symmetric digraph
RotationSystem:=function(digraph)
    local Neighbours, rotationSystem, facialCycles, cycle, i, act, neigh;

    Neighbours:=function(i,cycle)
        local pre, post;
        if i=1 then
            pre:=Last(cycle);
        else
            pre:=cycle[i-1];
        fi;

        if i=Length(cycle) then
            post:=cycle[1];
        else
            post:=cycle[i+1];
        fi;
        return [pre,post];
    end;

    rotationSystem:=List([1..DigraphNrVertices(digraph)],i->[]);
    facialCycles:=FacialCycles(digraph);

    for cycle in facialCycles do
        for i in [1..Length(cycle)] do
            act:=cycle[i];
            neigh:=Neighbours(i,cycle);
            if rotationSystem[act]=[] then
                rotationSystem[act]:=neigh;
            elif Length(rotationSystem[act])<>3 then
                if Last(rotationSystem[act])=neigh[1] then
                    Add(rotationSystem[act],neigh[2]);
                elif First(rotationSystem[act])=neigh[2] then
                    Add(rotationSystem[act],neigh[1]);
                else
                    return fail;
                fi;
            fi;
        od;
    od;
    return rotationSystem;
end;

# Computes all twisted subgraphs for the given surface
TwistedSubgraphs:=function(dualGraph, g, orientable)
    local ProjectivePlane, RemoveQuotient, CompleteTransformationList, GenerateK2m, K2m, Torus, KleinBottle;
    
    # Computes all twisted subgraphs for the projective plane
    ProjectivePlane:=function(dualGraph)
        local CreateCompleteSubdigraph;
        CreateCompleteSubdigraph:=function(n,vertices)
            local edges, i, v;
            edges:=[];
            for i in vertices do
                for v in Difference(vertices,[i]) do
                    Add(edges,[v,i]);
                od;
            od;
            return DigraphByEdges(edges,n);
        end;
        return List(CompleteSubgraphsOfGivenSize(Graph(dualGraph),4),g->CreateCompleteSubdigraph(DigraphNrVertices(dualGraph),g));
    end;

    # Completes the transformation list such that it has n entries
    CompleteTransformationList:=function(list,n)
        local i;
        list:=ShallowCopy(list);
        if Length(list)<n then
            for i in [Length(list)+1..n] do
                Add(list,i);
            od;
        fi;
        return list;
    end;

    # Generates the K_{2,m} for a given m
    GenerateK2m:=function(vertices,n,m)
        local incidenceList, partitionClasses, pair, i;

        incidenceList:=List([1..n],i->[]);
        partitionClasses:=[vertices{[1,2]},vertices{[3..m]}];
        for pair in partitionClasses do
            for i in pair do 
                incidenceList[i]:=Flat(Difference(partitionClasses,[pair]));
            od;
        od;
        return Digraph(incidenceList);
    end;

    # Computes the subgraphs of dualGraph isomorphic K_{2,2m} or K_{2,2m-1} depending on even
    K2m:=function(dualGraph,n,even)
        local digraphs, m, morphism, subdigr, list;
        digraphs:=[];
        for m in [1..n] do
            subdigr:=GenerateK2m([1..2*m+even],2*m+even,2*m+even);
            for morphism in MonomorphismsDigraphsRepresentatives(subdigr,dualGraph) do
                list:=CompleteTransformationList(ImageListOfTransformation(morphism),2*m+even);
                Add(digraphs,GenerateK2m(list{[1..2*m+even]},DigraphNrVertices(dualGraph),2*m+even));
            od;
        od;
        return Set(digraphs);
    end;

    # Computes all twisted subgraphs for the torus
    Torus:=function(dualGraph)
        local GenerateTripartiteGraphs, K222, subdigraphs;

        # Generates a tripartite graph with given partition classes
        GenerateTripartiteGraphs:=function(partitionClasses)
            local incidenceList,i,class;

            incidenceList:=List([1..Length(Flat(partitionClasses))],i->[]);
            for class in partitionClasses do
                for i in class do
                    incidenceList[i]:=Flat(Difference(partitionClasses,[class]));
                od;
            od;
            return Digraph(incidenceList);
        end;

        # Computes the subgraphs of dualGraph isomorphic K_{2,2,2}
        K222:=function(dualGraph)
            local subdigr,digraphs,morph,list,vertices;
            subdigr:=Digraph([[3,4,5,6,],[3,4,5,6],[1,2,5,6],[1,2,5,6],[1,2,3,4],[1,2,3,4]]);
            digraphs:=[];
            for morph in MonomorphismsDigraphsRepresentatives(subdigr,dualGraph) do
                list:=CompleteTransformationList(ImageListOfTransformation(morph),6);
                vertices:=list{[1..6]};
                Add(digraphs,GenerateTripartiteGraphs([vertices{[1,2]},vertices{[3,4]},vertices{[5,6]}]));
            od;
            return Set(digraphs);
        end;

        subdigraphs:=K222(dualGraph);
        subdigraphs:=Set(Concatenation(subdigraphs,K2m(dualGraph,Int(DigraphNrVertices(dualGraph)/2)-1,2)));

        return subdigraphs;
    end;

    # Computes all twisted subgraphs for the Klein bottle
    KleinBottle:=function(dualGraph)
        local A3, A5, A6, subdigraphs;

        # Computes the subgraphs of dualGraph isomorphic A_3
        A3:=function(dualGraph)
            local subdigr,digraphs,morph,list,vertices,incidenceList;
            subdigr:=DigraphDisjointUnion(CompleteDigraph(4),CompleteDigraph(4));
            digraphs:=[];
            for morph in MonomorphismsDigraphsRepresentatives(subdigr,dualGraph) do
                list:=CompleteTransformationList(ImageListOfTransformation(morph),8);
                vertices:=list{[1..8]};
                incidenceList:=List( [1..DigraphNrVertices(dualGraph)],i->[]);
                
                incidenceList[vertices[1]]:=vertices{[2..4]};
                incidenceList[vertices[2]]:=Concatenation(vertices{[3..4]},[vertices[1]]);
                incidenceList[vertices[3]]:=Concatenation(vertices{[1..2]},[vertices[4]]);
                incidenceList[vertices[4]]:=vertices{[1..3]};
                incidenceList[vertices[5]]:=vertices{[6..8]};
                incidenceList[vertices[6]]:=Concatenation(vertices{[7..8]},[vertices[5]]);
                incidenceList[vertices[7]]:=Concatenation(vertices{[5..6]},[vertices[8]]);
                incidenceList[vertices[8]]:=vertices{[5..7]};
                Add(digraphs,Digraph(incidenceList));
            od;
            return digraphs;
        end;

        # Computes the subgraphs of dualGraph isomorphic A_5
        A5:=function(dualGraph)
            local subdigr,digraphs,morph,list,vertices,incidenceList;
            subdigr:=Digraph([[2,3,4],[1,3,4],[1,2,4],[1,2,3,5,6,7],[4,6,7],[4,5,7],[4,5,6]]);
            digraphs:=[];
            for morph in MonomorphismsDigraphsRepresentatives(subdigr,dualGraph) do
                list:=CompleteTransformationList(ImageListOfTransformation(morph),7);
                vertices:=list{[1..7]};
                incidenceList:=List( [1..DigraphNrVertices(dualGraph)],i->[]);
                
                incidenceList[vertices[1]]:=vertices{[2..4]};
                incidenceList[vertices[2]]:=Concatenation(vertices{[3..4]},[vertices[1]]);
                incidenceList[vertices[3]]:=Concatenation(vertices{[1..2]},[vertices[4]]);
                incidenceList[vertices[4]]:=Concatenation(vertices{[1..3]},vertices{[5..7]});
                incidenceList[vertices[5]]:=Concatenation(vertices{[6..7]},[vertices[4]]);
                incidenceList[vertices[6]]:=Concatenation(vertices{[4..5]},[vertices[7]]);
                incidenceList[vertices[7]]:=vertices{[4..6]};
                
                Add(digraphs,Digraph(incidenceList));
            od;
            return digraphs;
        end;

        # Computes the subgraphs of dualGraph isomorphic A_6
        A6:=function(dualGraph)
            local subdigr,digraphs,morph,list,vertices,incidenceList,i;
            subdigr:=Digraph([[3,4,5,6],[3,4,5,6],[1,2,4],[1,2,3],[1,2,6],[1,2,5]]);
            digraphs:=[];
            for morph in MonomorphismsDigraphsRepresentatives(subdigr,dualGraph) do
                list:=CompleteTransformationList(ImageListOfTransformation(morph),6);
                vertices:=list{[1..6]};

                incidenceList:=List( [1..DigraphNrVertices(dualGraph)],i->[]);
                for i in [1,2] do
                    incidenceList[vertices[i]]:=vertices{[3..6]};
                od;
                incidenceList[vertices[3]]:=Concatenation(vertices{[1..2]},[vertices[4]]);
                incidenceList[vertices[4]]:=Concatenation(vertices{[1..2]},[vertices[3]]);
                incidenceList[vertices[5]]:=Concatenation(vertices{[1..2]},[vertices[6]]);
                incidenceList[vertices[6]]:=Concatenation(vertices{[1..2]},[vertices[5]]);
                Add(digraphs,Digraph(incidenceList));
            od;
            return digraphs;
        end;

        subdigraphs:=K2m(dualGraph,Int((DigraphNrVertices(dualGraph)-1)/2),1);
        subdigraphs:=Set(Concatenation(subdigraphs,A3(dualGraph)));
        subdigraphs:=Set(Concatenation(subdigraphs,A5(dualGraph)));
        subdigraphs:=Set(Concatenation(subdigraphs,A6(dualGraph)));
        return subdigraphs;
    end;

    if g=1 and not orientable then
        return ProjectivePlane(dualGraph);
    elif g=1 and orientable then
        return Torus(dualGraph);
    elif g=2 and not orientable then
        return KleinBottle(dualGraph);
    else   
        Error("Choose another genus and orientability");
    fi;
end;

Reembedding:=function(digraph, g, orientable)
    local DualGraph, RemoveTwistedSubgraphs, FindTwistedEdges, IsSimplicialEmbedding, Corners, FindPosition, NextNeighbour, NewEmbedding, DigraphsToSurf, facialCycles, rotationSystem, dualGraph, subdigraphs;

    # Computes the dual graph using the facial cycles
    DualGraph:=function(facialCycles)
        local edges, c1,c2,commonNodes;

        edges:=[];
        for c1 in [1..Length(facialCycles)-1] do
            for c2 in [c1+1..Length(facialCycles)] do
                commonNodes:=Intersection(facialCycles[c1],facialCycles[c2]);
                if commonNodes<>[] then
                    Add(edges,[c1,c2]);
                    Add(edges,[c2,c1]);
                fi;
            od;
        od;
        return DigraphByEdges(edges);
    end;

    # Removes subgraphs so that we cannot get isomorphic embeddings afterwards
    RemoveTwistedSubgraphs:=function(subdigraphs,digraph)
        local orbits, nodes, g, component, remove, l, pos;
        orbits:=[];
        nodes:=[];

        nodes:=List(subdigraphs,g->Filtered(DigraphConnectedComponents(g).comps,i->Length(i)>1)[1]);
        orbits:=List(nodes,n->Orbit(AutomorphismGroup(dualGraph),n,OnSets));
        
        for g in subdigraphs do
            remove:=[];
            for l in Difference(Filtered([1..Length(orbits)],i->nodes[Position(subdigraphs,g)] in orbits[i]),[Position(subdigraphs,g)]) do
                Add(remove,subdigraphs[l]);
            od;
            for l in remove do
                pos:=Position(subdigraphs,l);
                Remove(subdigraphs,pos);
                Remove(orbits,pos);
            od;
        od;
        return subdigraphs;
    end;

    # Compute the twisted arcs in the original graph by the twisted subgraph
    FindTwistedEdges:=function(digraph,facialCycles)
        local twistedEdges,edge;
        twistedEdges:=[];
        for edge in DigraphEdges(MaximalAntiSymmetricSubdigraph(digraph)) do
            Add(twistedEdges,Intersection(facialCycles[edge[1]],facialCycles[edge[2]]));
            Sort(Last(twistedEdges));
        od;
        return twistedEdges;
    end;

    # Deletes all twisted subgraphs that do not give a simplicial embedding
    IsSimplicialEmbedding:=function(facialCycles,twistedEdges)
        local cycle,mat,containedEdges,edge;
        for cycle in facialCycles do
            mat:=AdjacencyMatrixFromList(cycle,Maximum(Flat(facialCycles)));
            containedEdges:=List([1..Length(twistedEdges)],i->false);
            for edge in __SIMPLICIAL_EdgesFromAdjacencyMat(mat) do
                if edge in twistedEdges then
                    containedEdges[Position(twistedEdges,edge)]:=true;
                elif Reversed(edge) in twistedEdges then
                    containedEdges[Position(twistedEdges,Reversed(edge))]:=true;
                fi;
            od;
            if SizeBlist(containedEdges)=1 then
                return false;
            elif SizeBlist(containedEdges)=2 and not IsDuplicateFree(Flat(ListBlist(twistedEdges,containedEdges))) then
                return false;
            fi;
        od;
        return true;
    end;

    # Computes all corners of a graph by the rotation system
    Corners:=function(rotationSystem)
        local corners, v, pair;
        corners:=[];
        for v in [1..Length(rotationSystem)] do
            for pair in Combinations(rotationSystem[v],2) do
                Add(corners,[pair[1],v,pair[2]]);
            od;
        od;
        return corners;
    end;

    # Find the position of the set edge in the list edges
    FindPosition:=function(edge,edges)
        if edge in edges then
            return Position(edges,edge);
        else
            return Position(edges,Reversed(edge));
        fi;
    end;

    # Computes the next vertex in the face traversal procedure
    NextNeighbour:=function(vertex, pos, twisting, rotationSystem)
        if twisting then
                if pos>1 then
                    return rotationSystem[vertex][pos-1];
                else
                    return Last(rotationSystem[vertex]);
                fi;
            else
                if pos<Length(rotationSystem[vertex]) then
                    return rotationSystem[vertex][pos+1];
                else
                    return First(rotationSystem[vertex]);
                fi;
            fi;
    end;

    # Calculates the re-embedding for given twisted edges
    NewEmbedding:=function(twistedEdges,edges,rotationSystem)
        local cycles, corners, corner, last, previous, act, cycle, twisting, temp, pos, remove, i, cornerUsed,c;
        cycles:=[];
        corners:=Corners(rotationSystem);

        # Each corner has to be visited by a facial cycle
        while corners<>[] do
            corner:=corners[1];
            last:=corner[1];
            previous:=corner[2];
            act:=corner[3];
            cycle:=ShallowCopy(corner);

            # Checks how we have to start traversing to get a facial cycle that visits corner
            twisting:=twistedEdges[FindPosition([last,previous],edges)];
            v:=NextNeighbour(previous, Position(rotationSystem[previous],last),twisting,rotationSystem);
            if v<>act then
                twisting:=not twisting;
            fi;
    
            if twistedEdges[FindPosition([previous,act],edges)]=true then
                twisting:=not twisting;
            fi;

            # Traverse until we are back at the start vertex
            while act<>last do
                temp:=act;
                act:=NextNeighbour(act, Position(rotationSystem[act],previous),twisting,rotationSystem);
                previous:=temp;

                # Then the facial cycle is not simple
                if act in cycle and act<>last then 
                    return fail;
                elif act<>last then
                    Add(cycle,act);
                fi;

                # Adjust twisting
                if previous<act then
                    pos:=Position(edges,[previous,act]);
                else
                    pos:=Position(edges,[act,previous]);
                fi;
                if twistedEdges[pos]=true then
                    twisting:= not twisting;
                fi;
            od;
        
            remove:=[];

            # Remove the corners which are visited now
            for i in [1..Length(cycle)] do
                if i=1 then
                    cornerUsed:=[Last(cycle),First(cycle),cycle[2]];
                elif i=Length(cycle) then
                    cornerUsed:=[cycle[i-1],Last(cycle),First(cycle)];
                else
                    cornerUsed:=[cycle[i-1],cycle[i],cycle[i+1]];
                fi;
                if cornerUsed in corners then
                    pos:=Position(corners,cornerUsed);
                else 
                    pos:=Position(corners,Reversed(cornerUsed));
                    cornerUsed:=Reversed(cornerUsed);
                fi;
                if pos=fail then
                    return fail;
                else
                    Add(remove,cornerUsed);
                fi;
            od;
            for c in remove do
                Remove(corners,Position(corners,c));
            od;
            Add(cycles,cycle);
        od;
        return cycles;
    end;

    # Calculates for the twisted subgraphs the simplicial embeddings
    DigraphsToSurf:=function(digraph,digraphs,facialCycles,rotationSystem) 
        local res,subdigr,digraphUndirectedEdges,twistedEdges,cycles,umbr,cycle,s,contained,simp;
        res:=[];
        for subdigr in digraphs do
            twistedEdges:=FindTwistedEdges(subdigr,facialCycles);
            if IsSimplicialEmbedding(facialCycles,twistedEdges) then
                digraphUndirectedEdges:=DigraphEdges(MaximalAntiSymmetricSubdigraph(digraph));
                twistedEdges:=BlistList(digraphUndirectedEdges,twistedEdges);
                cycles:=NewEmbedding(twistedEdges,digraphUndirectedEdges,rotationSystem);
                if cycles<>fail then
                    umbr:=[];
                    for cycle in cycles do
                        Add(umbr,CycleFromList(cycle));
                    od;
                    s:=SimplicialSurfaceByUmbrellaDescriptor(umbr);
                    contained:=false;
                    for simp in res do
                        if IsIsomorphic(s,simp) then
                            contained:=true;
                        fi;
                    od;
                    if not contained then
                        Add(res,s);
                    fi;
                fi;
            fi;
        od;
        return res;
    end;

    facialCycles:=FacialCycles(digraph);
    rotationSystem:=RotationSystem(digraph);
    dualGraph:=DualGraph(facialCycles);
    subdigraphs:=TwistedSubgraphs(dualGraph, g, orientable);
    subdigraphs:=RemoveTwistedSubgraphs(subdigraphs,digraph);
    return DigraphsToSurf(digraph,subdigraphs,facialCycles,rotationSystem);
end;