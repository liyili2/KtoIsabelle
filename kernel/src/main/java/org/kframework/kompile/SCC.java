package org.kframework.kompile;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

public class SCC<V> {

    private boolean[] marked;        // marked[v] = has v been visited?
    private int[] id;                // id[v] = id of strong component containing v
    private int[] low;               // low[v] = low number of v
    private int pre;                 // preorder number counter
    private int count;               // number of strongly-connected components
    private Stack<Integer> stack;
    private Graph<V> graph;

    /**
     * Computes the strong components of the digraph <tt>G</tt>.
     * @param G the digraph
     */
    public SCC(Graph<V> g) {
    	this.graph = g;
        marked = new boolean[g.getVertexList().size()];
        stack = new Stack<Integer>();
        id = new int[g.getVertexList().size()]; 
        low = new int[g.getVertexList().size()];
        for (int v = 0; v < g.getVertexList().size(); v++) {
            if (!marked[v]) dfs(g, v);
        }

        // check that id[] gives strong components
        //assert check(G);
    }

    private void dfs(Graph<V> g, int v) { 
        marked[v] = true;
        low[v] = pre++;
        int min = low[v];
        stack.push(v);
        for (int w : g.getAdjacentIndices(g.getVertexList().get(v))) {
            if (!marked[w]) dfs(g, w);
            if (low[w] < min) min = low[w];
        }
        if (min < low[v]) {
            low[v] = min;
            return;
        }
        int w;
        do {
            w = stack.pop();
            id[w] = count;
            low[w] = g.getVertexList().size();
        } while (w != v);
        count++;
    }


    /**
     * Returns the number of strong components.
     * @return the number of strong components
     */
    public int count() {
        return count;
    }


    /**
     * Are vertices <tt>v</tt> and <tt>w</tt> in the same strong component?
     * @param v one vertex
     * @param w the other vertex
     * @return <tt>true</tt> if vertices <tt>v</tt> and <tt>w</tt> are in the same
     *     strong component, and <tt>false</tt> otherwise
     */
    public boolean stronglyConnected(int v, int w) {
        return id[v] == id[w];
    }

    /**
     * Returns the component id of the strong component containing vertex <tt>v</tt>.
     * @param v the vertex
     * @return the component id of the strong component containing vertex <tt>v</tt>
     */
    public int id(int v) {
        return id[v];
    }
    
    public int[] sccNums(){
    	return id;
    }
    
    public List<V> sccComponent(int v){
    	List<V> result = new ArrayList<V>();
    	for(int i = 0; i < id.length; ++i){
    		if(id[i] == v){
    			result.add(this.graph.getVertexList().get(i));
    		}
    	}
    	return result;
    }
}
