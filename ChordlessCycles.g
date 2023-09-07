Read("utilities.g");

# Compute all chordless cycles for a given symmetric digraph
AllChordlessCycles:=function(digraph)
    local BlockNeighbours, UnblockNeighbours, DegreeLabeling, Triplets, CCExtension, temp, T, C, blocked, triple;
    if not IsSymmetricDigraph(digraph) then
        return false;
    fi;
    BlockNeighbours:=function(digraph,v,blocked)
        local u;
        for u in OutNeighboursOfVertex(digraph,v) do
            blocked[u]:=blocked[u]+1;
        od;
        return blocked;
    end;

    UnblockNeighbours:=function(digraph,v,blocked)
        local u;
        for u in OutNeighboursOfVertex(digraph,v) do
            if blocked[u]>0 then
                blocked[u]:=blocked[u]-1;
            fi;
        od;
        return blocked;
    end;

    # Computes the degree labeling
    DegreeLabeling:=function(digraph)
        local degree,color,labeling,v,u,i,minDegree,x;

        degree:=List(DigraphVertices(digraph),i->0);
        color:=List(DigraphVertices(digraph),i->false);
        labeling:=List(DigraphVertices(digraph),i->0);
        degree:=List(DigraphVertices(digraph),i->OutDegreeOfVertex(digraph,i));

        for i in [1..DigraphNrVertices(digraph)] do
            minDegree:=DigraphNrVertices(digraph);
            for x in DigraphVertices(digraph) do
                if color[x]=false and degree[x]<minDegree then
                    v:=x;
                    minDegree:=degree[x];
                fi;
            od;
            labeling[v]:=i;
            color[v]:=true;
            for u in OutNeighboursOfVertex(digraph,v) do
                if color[u]=false then
                    degree[u]:=degree[u]-1;
                fi;
            od;
        od;
        return labeling;
    end;

    # Computes all possible triplets
    Triplets:=function(digraph)
        local T,C,u,pair,x,y,labels;
        T:=[];
        C:=[];
        for u in DigraphVertices(digraph) do
            for pair in Combinations(OutNeighboursOfVertex(digraph,u),2) do
                x:=pair[1];
                y:=pair[2];
                labels:=DigraphVertexLabels(digraph);
                if labels[u]<labels[x] and labels[x]<labels[y] then
                    if not IsDigraphEdge(digraph,x,y) then
                        Add(T,[x,u,y]);
                    else
                        Add(C,[x,u,y]);
                    fi;
                elif labels[u]<labels[y] and labels[y]<labels[x] then
                    if not IsDigraphEdge(digraph,x,y) then
                        Add(T,[y,u,x]);
                    else
                        Add(C,[y,u,x]);
                    fi;
                fi;
            od;
        od;
        return [T,C];
    end;

    # Extends a given chordless path if possible
    CCExtension:=function(digraph,path,C,key,blocked)
        local v,extendedPath,data;
        blocked:=BlockNeighbours(digraph,Last(path),blocked);
        for v in OutNeighboursOfVertex(digraph,Last(path)) do
            if DigraphVertexLabel(digraph,v)>key and blocked[v]=1 then
                extendedPath:=Concatenation(path,[v]);
                if IsDigraphEdge(digraph,v,First(path)) then  
                    Add(C,extendedPath);
                else
                    data:=CCExtension(digraph,extendedPath,C,key,blocked);
                    C:=data[1];
                    blocked:=data[2];
                fi;
            fi;
        od;
        blocked:=UnblockNeighbours(digraph,Last(path),blocked);
        return [C,blocked];
    end;

    SetDigraphVertexLabels(digraph,DegreeLabeling(digraph));
    temp:=Triplets(digraph);
    T:=temp[1];
    C:=temp[2];
    blocked:=List(DigraphVertices(digraph),i->0);
    while T<>[] do
        triple:=Remove(T);
        blocked:=BlockNeighbours(digraph,triple[2],blocked);
        temp:=CCExtension(digraph,triple,C,DigraphVertexLabel(digraph,triple[2]),blocked);
        C:=temp[1];
        blocked:=temp[2];
        blocked:=UnblockNeighbours(digraph,triple[2],blocked);
    od;
    return C;
end;;

# Tests if a cycle is separating in a given symmetric digraph.
# The cycle has to be given as a lower triangular adjacency matrix.
IsNonSeparating:=function(digraph,cycle)
    local edgesOfCycle, e, digraphRemoved;

    if not IsSymmetricDigraph(digraph) then
        return false;
    fi;

    edgesOfCycle:=[];
    for e in EdgesFromAdjacencyMat(cycle) do
        Append(edgesOfCycle,[e,Reversed(e)]);
    od;

    digraphRemoved:=DigraphRemoveEdges(digraph,edgesOfCycle);
    if IsConnectedDigraph(digraphRemoved) then
        return true;
    else
        return false;
    fi;
end;

# Computes for a 3-connected planar cubic symmetric digraph the unique vertex-faithful simplicial sphere
SphereOfDigraph:=function(digraph)
    local allCycles,umbrellaDesk,cycle;
    if not IsPlanarDigraph(digraph) or not IsBridgelessDigraph(digraph) or not IsSymmetricDigraph(digraph) or not IsCubic(digraph) then
        return false;
    fi;

    allCycles:=List(AllChordlessCycles(digraph),c->AdjacencyMatrixFromList(c,DigraphNrVertices(digraph)));
    allCycles:=Filtered(allCycles,c->IsNonSeparating(digraph,c));

    # Then the graph is not 3-connected
    if Length(allCycles)<>2+DigraphNrVertices(digraph)/2 then
        return false;
    fi;
    
    umbrellaDesk:=[];
    for cycle in allCycles do
        Add(umbrellaDesk,CycleFromList(NodesOfCycle(cycle)));
    od;
    return SimplicialSurfaceByUmbrellaDescriptor(umbrellaDesk);
end;