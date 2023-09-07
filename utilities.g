# We want to store graphs as adjacency matrices. This function
# turns a cycle into a boolean lower triangular matrix.
AdjacencyMatrixFromList := function(cycle, n)
    local mat, i, j, k;

    mat := []; 
    for i in [ 1 .. n] do
        mat[i] := BlistList([1..i],[]);
    od;

    for i in [ 1 .. Length(cycle)] do
        if i < Length(cycle) then 
                j := cycle[i+1];
        else j := cycle[1];
        fi;
        k := cycle[i]; 
        if k < j then 
            mat[j]:= UnionBlist(mat[j],BlistList( [1..j],[k] )); 
        elif j < k then 
            mat[k] := UnionBlist(mat[k],BlistList([1..k],[j]));
        fi;
    od;
    
        return mat;
end;;

# Calculate from a adjacency matrix the corresponding edges
EdgesFromAdjacencyMat := function(mat)
    local edges, i, j;

    edges := Set([]);
    for j in [1 .. Length(mat)] do
    edges := Union(edges, List(ListBlist([1..j],mat[j]), i-> [j,i] ));
    od;

	return edges;
end;;

# The function converts a boolean list describing one cycle 
# into list of nodes of the cycle.
NodesOfCycle:=function(cycle)
    local edges,firstNod,actualNode,nodes,e;

    edges:=EdgesFromAdjacencyMat(cycle);
    
    firstNod:=(edges[1])[1];
    actualNode:=(edges[1])[2];
    nodes:=[actualNode];
    Remove(edges,1);

    while actualNode<>firstNod do
        for e in edges do
            if e[1]=actualNode then
                actualNode:=e[2];
                Add(nodes,actualNode);
                Remove(edges,Position(edges,e)); 
            elif e[2]=actualNode then
                actualNode:=e[1];
                Add(nodes,actualNode);
                Remove(edges,Position(edges,e));
            fi; 
        od;
    od;

    return nodes;
end;;

# The function tests if a digraph is cubic
IsCubic:=function(digraph)
    if OutDegrees(digraph)=List(DigraphVertices(digraph),v->3) and InDegrees(digraph)=List(DigraphVertices(digraph),v->3) then
        return true;
    else   
        return false;
    fi;
end;;