package org.kframework.kompile;

import java.util.*;
import org.kframework.kil.*;

public class Element implements GlobalElement {
	HashMap<NonTerminal, List<Production>> theMap;
	
	public Element(){
		theMap = new HashMap<NonTerminal, List<Production>>();
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
}
