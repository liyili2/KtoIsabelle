package org.kframework.kompile;

import java.util.ArrayList;
import java.util.List;

import org.kframework.kil.NonTerminal;

public class GetNextDataTypeSort {
	Graph<NonTerminal> dataDependency;
	public GetNextDataTypeSort(Graph<NonTerminal> d){
		this.dataDependency = new Graph<NonTerminal>(d);
	}
	
	public List<NonTerminal> getNextSort(){
		for(int i = 0; i < this.dataDependency.getVertexList().size(); ++i){
			if(this.dataDependency
					.getAdjacentVertices((NonTerminal) this.dataDependency
							.getVertexList().get(i)).isEmpty()){
				NonTerminal result = (NonTerminal) this.dataDependency
						.getVertexList().get(i);
				this.dataDependency.removeVertex(result);
				List<NonTerminal> results = new ArrayList<NonTerminal>();
				results.add(result);
				return results;
			}
		}
		
		SCC<NonTerminal> components = new SCC<NonTerminal>(this.dataDependency);
		for(int sccNum = 0; sccNum < components.count(); ++sccNum){
			ArrayList<NonTerminal> theComponent
			         = (ArrayList<NonTerminal>) components.sccComponent(sccNum);
			if(!hasOutgoingEdge(theComponent)){
				return theComponent;
			}
		}
		return null;
	}
	
	private boolean hasOutgoingEdge(ArrayList<NonTerminal> component){
		
		for(int i = 0; i < component.size(); ++i){
			for(NonTerminal v : this.dataDependency
					.getAdjacentVertices(component.get(i))){
				if(!component.contains(v)){
					return true;
				}
			}
		}
		return false;
	}
}
