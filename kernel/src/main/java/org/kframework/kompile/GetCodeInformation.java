package org.kframework.kompile;

import java.util.ArrayList;
import java.util.Set;

import org.kframework.kil.loader.Context;
import org.kframework.kil.*;

public class GetCodeInformation
          extends AbstractVisitor<Void, GlobalElement, RuntimeException> {

	public GetCodeInformation(Context context) {
		super(context);
		// TODO Auto-generated constructor stub
	}
	
	/*
	 * this class is a visitor pattern to collect
	 * the information from a syntax.
	 */
	public GlobalElement visit(Definition node) {
        
		return this.visit((Module)(node.getItems().get(0)));		
	}
	
	/*
	 * this function takes a production and to generate a klabel
	 * for the input production.
	 * the way to generate the klabel is that
	 * we go through all the production item in the production, 
	 * and if a production item is terminal then we just put it
	 * into the string.
	 * if the production item is a nonterminal, then we use _ as
	 * the label and put it into the label string.
	 * in the production is a terminal or a nonTerminal.
	 * if the input production item is a terminal
	 */
	private String generateKLabel(Production item){
		String label = "'";
		for(ProductionItem p : item.getItems()){
			if(!(p instanceof Terminal)){
				label += "_";
			} else {
				label += ((Terminal)p).getTerminal();
			}
		}
		return label;
	}
	
	/*
	 *this function is to prepare a GlobalElement for the syntax node.
	 *for a syntax node, we first see if the priority block of the syntax
	 *is a function or not. Since every input syntax node will assume to have
	 *only one prioprity block and only one production, so that we can assume
	 *the function getSyntaxByTag will return a production with only one node.
	 *Later on, if the production has function label, then collect the following
	 *information: the klabel for the function node, the argument list with NonTerminals
	 *the target sort of the function. For example:
	 * syntax AExp ::= goto(Int, Int) [function]
	 * the klabel for the function production is 'goto(_), the argument list is [Int, Int]
	 * the target sort is AExp. It is trivial to call it target sort because if we view
	 * goto is a function, then the function takes two input arguments: Int and Int, and then
	 * return the user an AExp item.
	 * 
	 * On the other hand, if the input item is not a function production, then
	 * we collection the target sort and the production for the syntax node.
	 */
    public GlobalElement visit(Syntax node) throws RuntimeException {
    	
    	if(node.getPriorityBlocks().isEmpty()){
    		return new ThePair();
    	}
    	Set<Production> prods = node.getSyntaxByTag("function", context);
    	ArrayList<Production> items = new ArrayList<Production>(prods);
    	if(!prods.isEmpty()){
    		ArrayList<NonTerminal> arguments = new ArrayList<NonTerminal>();
    		for(int i = 0; i < items.get(0).getItems().size(); ++i){
    			if(items.get(0).getItems().get(i) instanceof NonTerminal){
    				arguments.add((NonTerminal) items.get(0).getItems().get(i));
    			}
    		}
    		FunctionElement result =
    				new FunctionElement(generateKLabel(items.get(0)),arguments,node.getChild(null));
    		return result;
    	} else {
    		ThePair aPair = new ThePair();
        	aPair.add((NonTerminal)node.getChild(null),
        			(Production)(((PriorityBlock)(node.getPriorityBlocks().
        					get(0))).getProductions().get(0)));
        	return aPair;
    	}
    }
    
    /*
     * this function go through every line in the module, and for each
     * line, if the item is a syntax, then it will call the syntax visitor
     * in this class to collect the information, otherwise, we skip.
     */
    public GlobalElement visit(Module node) throws RuntimeException {
    	
    	Element syntaxElement = new Element();
    	for(int i = 0; i < node.getItems().size(); ++i){
    		
    		if(node.getItems().get(i) instanceof Syntax){
    			GlobalElement aPair = this.visit((Syntax)node.getItems().get(i));
    			if(aPair instanceof ThePair){
    				syntaxElement.add(((ThePair)aPair).sort,
    						((ThePair)aPair).production);
    			} else if(aPair instanceof FunctionElement){
    				syntaxElement.add(((FunctionElement)aPair).klabel
    						, ((FunctionElement)aPair).arguments, ((FunctionElement)aPair).result);
    			}
    		}
    	}
    	return syntaxElement;
    }

    //belows are default functions without any meaning.
    @Override
	public GlobalElement defaultReturnValue(ASTNode node, Void p) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public <T extends ASTNode> T processChildTerm(T child,
			GlobalElement childResult) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean visitChildren() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean cache() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public <T extends ASTNode> T copy(T original) {
		// TODO Auto-generated method stub
		return null;
	}

}