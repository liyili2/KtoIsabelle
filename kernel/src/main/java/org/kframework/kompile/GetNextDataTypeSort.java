package org.kframework.kompile;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import org.kframework.kil.NonTerminal;

public class GetNextDataTypeSort {
	Graph<NonTerminal> dataDependency;
	SCC resultGraph;
	ArrayList<HashSet<NonTerminal>> sccComponents;
	public GetNextDataTypeSort(Graph<NonTerminal> d){
		this.dataDependency = new Graph<NonTerminal>(d);
		this.resultGraph = new SCC(d);
		getSCC();
	}
	
	//sepearate the vetecis into seceral pieces by SCC
	private void getSCC(){
		this.sccComponents = new ArrayList<HashSet<NonTerminal>>();
		for(int i = 0; i < resultGraph.count(); ++i){
			HashSet<NonTerminal> resultSet = new HashSet<NonTerminal>();
			for(int j = 0; j < this.dataDependency.getVertexList().size(); ++j){
				if(resultGraph.id(j) == i){
					resultSet.add((NonTerminal) this.dataDependency.getVertexList().get(j));
				}
			}
			sccComponents.add(resultSet);
		}
	}
	
	public List<NonTerminal> getNextSort(){
		for(int i = 0; i < this.sccComponents.size(); ++i){
			if(!this.hasOutgoingEdge(this.sccComponents.get(i))){
				ArrayList<NonTerminal> removeList
				    = new ArrayList<NonTerminal>(this.sccComponents.get(i));
				for(int j = 0; j < removeList.size(); ++j){
					this.dataDependency.removeVertex(removeList.get(j));
				}
				this.resultGraph = new SCC(this.dataDependency);
				this.sccComponents = new ArrayList<HashSet<NonTerminal>>();
				getSCC();
				return (List<NonTerminal>) removeList;
			}
		}
		return null;
	}
	
	private boolean hasOutgoingEdge(HashSet<NonTerminal> component){
		
		ArrayList<NonTerminal> componentList
		            = new ArrayList<NonTerminal>(component);
		for(int i = 0; i < componentList.size(); ++i){
			for(NonTerminal v : this.dataDependency
					.getAdjacentVertices(componentList.get(i))){
				if(!component.contains(v)){
					return true;
				}
			}
		}
		return false;
	}
}
