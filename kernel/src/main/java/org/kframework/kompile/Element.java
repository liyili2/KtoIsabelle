package org.kframework.kompile;

import java.util.*;
import org.kframework.kil.*;

public class Element implements GlobalElement {
	HashMap<NonTerminal, List<Production>> theMap;
	List<FunctionElement> functionDecls;
	List<Production> kResultProductions;
	
	public Element(){
		theMap = new HashMap<NonTerminal, List<Production>>();
		functionDecls = new ArrayList<FunctionElement>();
		kResultProductions = new ArrayList<Production>();
	}
	
	public void add(NonTerminal key, Production value){
		
		if(theMap.get(key) == null){
			ArrayList<Production> newValue = new ArrayList<Production>();
			newValue.add(value);
			theMap.put(key, newValue);
			return;
		}
		
		theMap.get(key).add(value);
	}
	
	public void add(String k, List<NonTerminal> a, NonTerminal r){
		
		FunctionElement result = new FunctionElement(k,a,r);
		this.functionDecls.add(result);
	}
}
