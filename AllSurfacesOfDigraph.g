Read("ChordlessCycles.g");

# Compute all cycles of a given symmetric digraph
AllCyclesOfGraph:=function(digraph)

	local NodesOfCycle, CycleOnEdge, CycleBasisOfGraph, XORAdjacencyMatrices,
	MultipleCyclesInMatrix, cyclebasis, allcycles, nullmat, mat, i, k, pos, neighs,c,cycle;

    # The function converts a boolean list describing one or more cycles 
    # into lists of nodes of the cycles.
    NodesOfCycle:=function(cycle)
        local edges,firstNod,actualNod,nodes,found,e,cycles;

        edges:=EdgesFromAdjacencyMat(cycle);
        cycles:=[];
        # We have to use each edge exactly one time
        while edges<>[] do
            firstNod:=(edges[1])[1];
            actualNod:=(edges[1])[2];
            Remove(edges,1);
            nodes:=[actualNod];
            # Walk along the cycle
            while actualNod<>firstNod do
                found:=false;
                for e in edges do
                    if found=false then
                        if e[1]=actualNod then
                            actualNod:=e[2];
                            Add(nodes,actualNod);
                            Remove(edges,Position(edges,e));
                            found:=true; 
                        elif e[2]=actualNod then
                            actualNod:=e[1];
                            Add(nodes,actualNod);
                            Remove(edges,Position(edges,e));
                            found:=true;
                        fi;
                    fi;
                od;
            od;
            Add(cycles,nodes);
        od;
        return cycles;
    end;	
	   
	# Find a cycle in the original graph all of whose edges are in
	# tree except for the edge e.
	CycleOnEdge := function( tree, root, e )
			
			local cycle, i, path1, path2, l1, l2;

			if e[1] = e[2] then
				Error("CycleOnEdge: edge is  a loop");
				return false;
			fi;

			# first find paths from the root to the two vertices of e
			if root = e[1] then path1 := [root];
			else path1 := DigraphPath(tree, root, e[1])[1]; fi;
			if root = e[2] then path2 := [root];
			else path2 := DigraphPath(tree, root, e[2])[1]; fi;
			l1 := Length(path1); l2 := Length(path2);

			# now skip the common entries in the path
			cycle := []; i := 1;
			while i <= Minimum(l1,l2) and path1[i] = path2[i]  do
				  i := i + 1;
			od;
		
			cycle := [path1[i-1]];
			Append(cycle, path1{[i..l1]});
			Append(cycle, Reversed(path2{[i..l2]}));

			return AdjacencyMatrixFromList(cycle,DigraphNrVertices(tree));
	end;;

	# This function computes a cycle basis for the undirected graph
	# dig, which is assumed to be a symmetric digraph.
	# The cycle Basis consists of lower triangular matrices whose
	# entries are boolean lists.
	CycleBasisOfGraph := function( dig )

		local tree, dige, base, root, e;

		if not IsSymmetricDigraph(dig) then
			Error("the digraph is assumed to be symmetric");
		fi;

		base := Set([]);
		tree := UndirectedSpanningTree(dig);
		dige := DigraphEdges(tree);

		root := DigraphVertices(dig)[1];
		
		for e in DigraphEdges(dig) do
			if not e in dige then
				AddSet(base, CycleOnEdge(tree,root, e));
			fi;
		od;
		return base;
	end;;

	# This method combines two adjacency matrices with the operator XOR.
	XORAdjacencyMatrices := function( mat1, mat2 )

		local j, res, nd;

			res :=[];
			for j in [1.. Length(mat1)] do
				nd := IntersectionBlist(mat1[j],mat2[j]);
				FlipBlist(nd);
				res[j] := IntersectionBlist( UnionBlist(mat1[j],mat2[j]), nd );
			od;

			return res;
	end;;	

	cyclebasis := CycleBasisOfGraph( digraph );
	
	if cyclebasis=[] then
		return [];
	fi;

	neighs := OutNeighbours(digraph);
	allcycles := [];
	
	nullmat := XORAdjacencyMatrices(cyclebasis[1],cyclebasis[1]);
	for k in [0..2^Length(cyclebasis)-1] do
		# combine the matrices encoded by k
		mat := nullmat;
		i := k;
		pos := 0;
		while i>0 do
			pos := pos + 1;
			if i mod 2 <> 0 then
				mat := XORAdjacencyMatrices(mat,cyclebasis[pos]);
			fi;
			i := Int(i/2);
		od;

		if SizeBlist(Flat(mat))<>0 then
			for c in NodesOfCycle(mat) do
				cycle:=AdjacencyMatrixFromList(c,Length(mat));
				if not cycle in allcycles then
					Add(allcycles,cycle);
				fi;
			od; 
		fi;
	 od;
	return allcycles;
end;

# Compute all simplicial embeddings or all vertex-faithful embeddings of a given cubic symmetric digraph
AllSimplicialEmbeddingsOfDigraph:=function(digraph,vertexFaithful)
		
		local allCycles,edgesOfGraph, faces,edgesOfCycles,CyclesOfEdges,cyclesOfEdges,FindSurface,FindCycleComb,
        cycle,cyclePair,IsPartOf,possibleCyclesPairs,commonEdges,Possible,e;

		if IsMultiDigraph(digraph) or DigraphHasLoops(digraph) or not IsSymmetricDigraph(digraph) or not IsConnectedDigraph(digraph) or not IsCubic(digraph) then
            Error("SimplicialSurfaceOfDigraph: Given digraph has to be simple, symmetric and connected");
        fi;
        if vertexFaithful then
            allCycles:=List(AllChordlessCycles(digraph),c->AdjacencyMatrixFromList(c,DigraphNrVertices(digraph)));
            allCycles:=Filtered(allCycles,c->IsNonSeparating(digraph,c));
        else
	    	allCycles:=AllCyclesOfGraph(digraph);
        fi;
     
		edgesOfGraph:=Filtered(DigraphEdges(digraph),e->not IsSortedList(e));

		edgesOfCycles:=[];
		for cycle in [1..Length(allCycles)] do;
			edgesOfCycles[cycle]:=List(EdgesFromAdjacencyMat(allCycles[cycle]),e->Position(edgesOfGraph,e));
		od;

		possibleCyclesPairs:=[];
		for e in [1..Length(edgesOfGraph)] do
			possibleCyclesPairs[e]:=[];
		od;

		for cyclePair in IteratorOfCombinations([1..Length(allCycles)],2) do
			commonEdges:=Intersection(edgesOfCycles[cyclePair[1]],edgesOfCycles[cyclePair[2]]);
			if Length(commonEdges)=1 and vertexFaithful then
				Add(possibleCyclesPairs[commonEdges[1]],cyclePair);
			elif not vertexFaithful then
				for e in commonEdges do
					Add(possibleCyclesPairs[e],cyclePair);
				od;
			fi;
		od;

		faces:=[];

		# The function returns a list that stores a Boolean list for each edge. 
		# An entry in the list is true if the edge is included in this cycle.
		CyclesOfEdges:=function()
			local cyclesOfEdges,e,cyclesOfEdge,cycle;
			cyclesOfEdges:=[];

			for e in [1..Length(edgesOfGraph)] do
				cyclesOfEdge:=BlistList([1..Length(allCycles)],[]);
				for cycle in [1..Length(allCycles)] do
					if e in edgesOfCycles[cycle] then
						cyclesOfEdge[cycle]:=true;
					fi;
				od;
				cyclesOfEdges[e]:=cyclesOfEdge;
			od;
			return cyclesOfEdges;
		end;;

		cyclesOfEdges:=CyclesOfEdges();;
		
		# The function checks whether the given cycle has at most one common edge with one element of cycles.
		Possible:=function(cycle,cycles)
			local c;
			for c in cycles do
				if Length(Intersection(edgesOfCycles[cycle],edgesOfCycles[c]))>1 then	
					return false;
				fi; 
			od;
			return true;
		end;;

		IsPartOf:=function(face,faces)
			local f;
			for f in faces do
				if IsIsomorphic(f,face) then
					return true;
				fi;
			od;
			return false;
		end;;

		FindSurface:=function(graph)
			local smallCy, cycle,cyclesOfFace,usedEdges,edgesOfCycle,c,edge,cyclesToUse; 
			
			# if we search vertex-faithful simplicial surfaces all cycles of length three and four have to be part of the resulting cycle combination
			if vertexFaithful and IsIsomorphicDigraph(graph, CompleteDigraph(4)) then
				smallCy:=Filtered([1..Length(allCycles)], c->SizeBlist(Flat(allCycles[c]))<4);
				smallCy:=BlistList([1..Length(allCycles)],smallCy);
			elif vertexFaithful then
				smallCy:=Filtered([1..Length(allCycles)], c->SizeBlist(Flat(allCycles[c]))<5);
				smallCy:=BlistList([1..Length(allCycles)],smallCy);
			fi;
			
			for cycle in [1..Length(allCycles)] do
				
				cyclesOfFace:=BlistList([1..Length(allCycles)],[cycle]);
				
				if vertexFaithful then
					cyclesOfFace:=UnionBlist(cyclesOfFace, smallCy);
				fi;
				
				usedEdges:=ListWithIdenticalEntries(Length(edgesOfGraph),0);
				
				edgesOfCycle:=[];
				for c in ListBlist([1..Length(allCycles)],cyclesOfFace) do
					edgesOfCycle:=Concatenation(edgesOfCycle,edgesOfCycles[c]);
				od;

				for edge in edgesOfCycle do
					usedEdges[edge]:=usedEdges[edge]+1;
				od;

                		if ForAll(usedEdges,i->i<3) then
					cyclesToUse:=BlistList([1..Length(allCycles)],[cycle+1..Length(allCycles)]);
                   	 		cyclesToUse:=DifferenceBlist(cyclesToUse,cyclesOfFace);
                    
                   			FindCycleComb(cyclesOfFace,usedEdges,1,graph,cyclesToUse);
                		fi;
			od;
		end;;

		# This is a recursive function that searches an admissible cycle combination.  
		# usedEdges stores how often each edge is used.
		# We assume that usedEdges is permissible, that mean each entry is at most two and the cycles overlap at most in one edge 
		# if we search vertex-faithful surfaces.
		# vertexCycleComb is a Boolean list which stores all cycles we used so far.
		# k is the position of the edge that we want to consider where all previous edges are already used twice. We start with the first edge.
		# CyclesToUse is a Boolean list that stores all the cycles that we are currently allowed to use.
		# A cycle must not be used if it contains an edge that has already been used twice.
		FindCycleComb:=function(vertexCycleComb,usedEdges,k,graph,cyclesToUse)
			local admissible, cycleRem, face,umbrellaDesk,kcycle,permissible,cycle,j,e,newUsedEdges,newVertexCycleComb,edgesOfCycle,newCyclesToUse,cy;
		
			if ForAll(usedEdges,i->i=2) then
                admissible:=true;
                if vertexFaithful then
                    for cycle in ListBlist([1..Length(vertexCycleComb)],vertexCycleComb) do
                        cycleRem:=ShallowCopy(vertexCycleComb);
                        cycleRem[cycle]:=false;
                        if not Possible(cycle, ListBlist([1..Length(vertexCycleComb)],cycleRem)) then
                            admissible:=false;
                        fi;
                    od;
                fi;

                if admissible then
                    umbrellaDesk:=[];

                    for cycle in ListBlist([1..Length(vertexCycleComb)],vertexCycleComb) do
                        Add(umbrellaDesk,CycleFromList(NodesOfCycle(allCycles[cycle])));
                    od;
    
                    face:=SimplicialSurfaceByUmbrellaDescriptor(umbrellaDesk);
                    if not IsPartOf(face,faces) then
                        Add(faces,face);
                    fi;
                fi;
			else
				if usedEdges[k]=1 and SizeBlist(cyclesToUse)>0 then
				
					kcycle:=IntersectionBlist(cyclesOfEdges[k],cyclesToUse);

					# Checks which cycle we can add to our combination such that k is contained twice and the new combination is permissible.
					for j in ListBlist([1..Length(kcycle)],kcycle) do
							
						if not vertexFaithful or Possible(j,ListBlist([1..Length(allCycles)],vertexCycleComb))then
							
							# permissible stores if the current vertexCycleComb together with the new cycle is admissible. 
							permissible:=true;

							edgesOfCycle:=edgesOfCycles[j];
								
							for e in edgesOfCycle do
								if usedEdges[e]>=2 then
									permissible:=false;
								fi;
							od;
								
							if permissible then

								newUsedEdges:=ShallowCopy(usedEdges);
								for e in edgesOfCycle do
									newUsedEdges[e]:=usedEdges[e]+1;
								od;

								newVertexCycleComb:=ShallowCopy(vertexCycleComb);
								newVertexCycleComb[j]:=true;

								newCyclesToUse:=DifferenceBlist(cyclesToUse,kcycle);
			
								for e in edgesOfCycle do
									if newUsedEdges[e]=2 and e>k then
										newCyclesToUse:=DifferenceBlist(newCyclesToUse,cyclesOfEdges[e]);
									fi;
								od;	
								FindCycleComb(newVertexCycleComb,newUsedEdges,k+1,graph,newCyclesToUse);
							fi;
						fi;
					od;
				elif usedEdges[k]=0 and SizeBlist(cyclesToUse)>0 then
						
					# Checks which cycle pair of k can be added to our cycle combination
					for j in possibleCyclesPairs[k] do
						
						if cyclesToUse[j[1]] and cyclesToUse[j[2]] and (not vertexFaithful or Possible(j[1],
							ListBlist([1..Length(allCycles)],vertexCycleComb)) and Possible(j[2],ListBlist([1..Length(allCycles)],
							vertexCycleComb))) then
							edgesOfCycle:=Union(edgesOfCycles[j[1]],edgesOfCycles[j[2]]);						

							# permissible stores if the current vertexCycleComb together with the new cycle is admissible. 
							permissible:=true;
								
							for e in edgesOfCycle do
								if usedEdges[e]>=2 then
									permissible:=false;
								fi;
							od;

							if not vertexFaithful then
								for e in Intersection(edgesOfCycles[j[1]],edgesOfCycles[j[2]]) do
									if usedEdges[e]>=1 then
										permissible:=false;
									fi;
								od;
							fi;

							if permissible then 
							
								newUsedEdges:=ShallowCopy(usedEdges);
								for e in edgesOfCycle do
									newUsedEdges[e]:=newUsedEdges[e]+1;
								od;
									
								if vertexFaithful then
									newUsedEdges[k]:=newUsedEdges[k]+1;
								else
									for e in Intersection(edgesOfCycles[j[1]],edgesOfCycles[j[2]]) do
										newUsedEdges[e]:=newUsedEdges[e]+1;
									od;
								fi;
								
								newVertexCycleComb:=ShallowCopy(vertexCycleComb);
								newVertexCycleComb[j[1]]:=true;
								newVertexCycleComb[j[2]]:=true;

								kcycle:=IntersectionBlist(cyclesOfEdges[k],cyclesToUse);
								newCyclesToUse:=DifferenceBlist(cyclesToUse,kcycle);

								for e in edgesOfCycle do
									if newUsedEdges[e]=2 and e>k then
										newCyclesToUse:=DifferenceBlist(newCyclesToUse,cyclesOfEdges[e]);
									fi;
								od;	
								FindCycleComb(newVertexCycleComb,newUsedEdges,k+1,graph,newCyclesToUse);
							fi;
						fi;
					od;
				elif usedEdges[k]=2 then
					FindCycleComb(vertexCycleComb,usedEdges,k+1,graph,cyclesToUse);
				fi;
			fi;
		end;;

		FindSurface(digraph);
		return faces;
end;