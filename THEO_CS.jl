### A Pluto.jl notebook ###
# v0.19.25

using Markdown
using InteractiveUtils

# ╔═╡ 8cc13850-e8d3-11ed-2309-8f80bad85bd2
begin
	begin
		using Graphs
		
		# Define the adjacency matrix
		adj_matrix = [
		    0 1 0;
		    1 0 1;
		    0 0 0
		]
		
		# Create the directed graph
		graph = DiGraph(adj_matrix)
	end
end

# ╔═╡ Cell order:
# ╠═8cc13850-e8d3-11ed-2309-8f80bad85bd2
