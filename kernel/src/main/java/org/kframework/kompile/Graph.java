package org.kframework.kompile;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

public class Graph<V> {

	private HashMap<V, ArrayList<Edge<V>>> adjacencyList;

	/**
	 * This list holds all the vertices so that we can iterate over them in the
	 * toString function
	 */
	private ArrayList<V> vertexList;

	private boolean directed;

	public Graph(boolean isDirected) {
		directed = isDirected;
		adjacencyList = new HashMap<V, ArrayList<Edge<V>>>();
		vertexList = new ArrayList<V>();
	}
	
	public Graph(Graph<V> g){
		this.directed = g.directed;
		this.vertexList = new ArrayList<V>(g.vertexList);
		this.adjacencyList = new HashMap<V, ArrayList<Edge<V>>>(g.adjacencyList);
	}
	
	public void add(V vertex) {
		
		if(vertexList.contains(vertex))
			return;
		// Add the new vertex to the adjacencyList with it's list of connected
		// nodes
		ArrayList<Edge<V>> connectedVertices = new ArrayList<Edge<V>>();
		adjacencyList.put(vertex, connectedVertices);
		vertexList.add(vertex);
	}

	public void add(V vertex, ArrayList<Edge<V>> connectedVertices) {
		
		if(vertexList.contains(vertex))
			return;
		// Add the new vertex to the adjacencyList with it's list of connected
		// nodes
		adjacencyList.put(vertex, connectedVertices);
		vertexList.add(vertex);
		// If this is an undirected graph, every edge needs to represented
		// twice, once in the added vertex's list and once in the list of each
		// of the vertex's connected to the added vertex

			for (Edge<V> vertexConnectedToAddedVertex : connectedVertices) {
				ArrayList<Edge<V>> correspondingConnectedList = adjacencyList
						.get(vertexConnectedToAddedVertex.getVertex());
				// The added vertex's connections might not be represented in
				// the Graph yet, so we implicitly add them
				if (correspondingConnectedList == null) {
					adjacencyList.put(vertexConnectedToAddedVertex.getVertex(),
							new ArrayList<Edge<V>>());
					vertexList.add(vertexConnectedToAddedVertex.getVertex());
					correspondingConnectedList = adjacencyList
							.get(vertexConnectedToAddedVertex.getVertex());
				}
				
				if (!directed) {
					// The weight from one vertex back to another in an undirected
					// graph is equal
					int weight = vertexConnectedToAddedVertex.getWeight();
					correspondingConnectedList.add(new Edge<V>(vertex, weight));
				}
			}
		
	}

	public boolean addArc(V source, V end, int weight) {
		if (!directed) {
			return false;
		}

		if (!adjacencyList.containsKey(source)) {
			ArrayList<Edge<V>> tempList = new ArrayList<Edge<V>>();
			tempList.add(new Edge<V>(end, weight));
			add(source, tempList);
			return true;
		}
		
		if (!adjacencyList.containsKey(end)) {
			ArrayList<Edge<V>> tempList = new ArrayList<Edge<V>>();
			add(end, tempList);
		}
		

		if(!containEdge(this.adjacencyList.get(source), end)){
			adjacencyList.get(source).add(new Edge<V>(end, weight));
		}
		return true;
	}
	
	public boolean containEdge(ArrayList<Edge<V>> edges, V end){
		for(int i = 0; i < edges.size(); ++i){
			if(edges.get(i).getVertex().equals(end)){
				return true;
			}
		}
		return false;
	}

	public boolean addEdge(V vertexOne, V vertexTwo, int weight) {
		if (directed) {
			return false;
		}
		
		if (!adjacencyList.containsKey(vertexOne)) {
			ArrayList<Edge<V>> tempList = new ArrayList<Edge<V>>();
			tempList.add(new Edge<V>(vertexTwo, weight));
			add(vertexOne, tempList);
			return true;
		}

		if (!adjacencyList.containsKey(vertexTwo)) {
			ArrayList<Edge<V>> tempList = new ArrayList<Edge<V>>();
			tempList.add(new Edge<V>(vertexOne, weight));
			add(vertexTwo, tempList);
			return true;
		}

		adjacencyList.get(vertexOne).add(new Edge<V>(vertexTwo, weight));
		adjacencyList.get(vertexTwo).add(new Edge<V>(vertexOne, weight));
		return true;
	}

	/**
	 * This method returns a list of all adjacent vertices of the give vertex without weight
	 * 
	 * @param vertex the source vertex 
	 * @return an array list containing the vertices
	 */
	public ArrayList<V> getAdjacentVertices(V vertex){
		ArrayList<V> returnList = new ArrayList<V>();
		for (Edge<V> edge : adjacencyList.get(vertex)) {
			returnList.add(edge.getVertex());
		}
		return returnList;
	}
	
	//return indices of edges
	public ArrayList<Integer> getAdjacentIndices(V vertex){
		ArrayList<Integer> returnList = new ArrayList<Integer>();
		for (Edge<V> edge : adjacencyList.get(vertex)) {
			returnList.add(this.vertexList.indexOf(edge.getVertex()));
		}
		return returnList;
	}
	
	public double getDistanceBetween(V source, V end){
		 for (Edge<V> edge : adjacencyList.get(source)) {
			if (edge.getVertex() == end){
				return edge.getWeight();
			}
		}
		return Double.POSITIVE_INFINITY;
	}
	
	public ArrayList<V> getVertexList() {
		return vertexList;
	}
	
	public void removeVertex(V vertex){
		this.vertexList.remove(vertex);
		this.adjacencyList.remove(vertex);
		for(int i = 0; i < this.vertexList.size(); ++i){
			for(int j = 0; j < this.adjacencyList
					.get(this.vertexList.get(i)).size(); ++j){
				if(this.adjacencyList
					.get(this.vertexList.get(i)).get(j).getVertex().equals(vertex)){
					this.adjacencyList.get(this.vertexList.get(i))
					.remove(this.adjacencyList.get(this.vertexList.get(i)).get(j));
				}
			}
		}
	}
	
	public String toString() {
		String s = "";
		for (V vertex : vertexList) {
			s += vertex.toString();
			s += " : ";
			s += adjacencyList.get(vertex);
			s += "\n";
		}
		return s;
	}
}