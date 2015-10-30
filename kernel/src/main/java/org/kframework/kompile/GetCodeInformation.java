package org.kframework.kompile;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;

import org.kframework.compile.utils.SyntaxByTag;
import org.kframework.kil.loader.Context;
import org.kframework.kil.*;
import org.kframework.utils.errorsystem.KExceptionManager;

public class GetCodeInformation
          extends AbstractVisitor<Void, GlobalElement, RuntimeException> {

    private static final String STRICT = "strict";
    private static final String SEQSTRICT = "seqstrict";

    
	public GetCodeInformation(Context context) {
		super(context);
		// TODO Auto-generated constructor stub
	}
	
    /*
     * this function will change the name of symbols in K
     * to name of english characters in Isabelle.
     */
    private String generateName(String t){
    	
    	String value = "";
    	for(int i = 0; i < t.length(); ++i) {
    		if(t.charAt(i) == '\''){
    			if(i != 0) {
    				value += "Top";
    			}
    		} else if (t.charAt(i) == '_') {
    			value += "X";
    		} else if(t.charAt(i) == '(' || t.charAt(i) == ')') {
    			value += "Br";
    		} else if(t.charAt(i) == '{' || t.charAt(i) == '}') {
    			value += "Bl";
    		} else if(t.charAt(i) == '[' || t.charAt(i) == ']') {
    			value += "Bm";
    		} else if(t.charAt(i) == '=') {
    			value += "Eq";
    		} else if(t.charAt(i) == '|') {
    			value += "Sl";
    		} else if(t.charAt(i) == '&') {
    			value += "An";
    		} else if(t.charAt(i) == '@') {
    			value += "At";
    		} else if(t.charAt(i) == '*') {
    			value += "Times";
    		} else if(t.charAt(i) == '+') {
    			value += "Plus";
    		} else if(t.charAt(i) == '-') {
    			value += "Minus";
    		} else if(t.charAt(i) == '/') {
    			value += "Div";
    		} else if(t.charAt(i) == '<') {
    			value += "Less";
    		} else if(t.charAt(i) == '>') {
    			value += "Greater";
    		} else if(t.charAt(i) == '!') {
    			value += "Not";
    		} else if(t.charAt(i) == ';') {
    			value += "End";
    		} else if(t.charAt(i) == ':') {
    			value += "To";
    		} else {
    			value += t.charAt(i);
    		}
    	}
    	if(value.length() >= 1) {
    		if(value.charAt(0) <= 'z' && value.charAt(0) >= 'a') {
    			value = value.substring(0, 1).toUpperCase()
    					+ value.substring(1, value.length());
    		} else if(value.charAt(0) <= '9' && value.charAt(0) >= '0'){
    			value = "Num"+value;
    		}
    	}
    	return value;
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
    				new FunctionElement(generateKLabel(items.get(0)),
    						generateName(generateKLabel(items.get(0))), arguments,node.getChild(null));
    		return result;
    	} else if(((Production)(((PriorityBlock)(node.getPriorityBlocks().
				get(0))).getProductions().get(0))).isSubsort()){
    		if(((Production)(((PriorityBlock)(node.getPriorityBlocks().
    				get(0))).getProductions().get(0))).getItems().get(0) instanceof NonTerminal){
    			SubSortElement result = 
    					new SubSortElement(node.getChild(null).toString()
    							+"Of"+((Production)(((PriorityBlock)(node.getPriorityBlocks().
        				get(0))).getProductions().get(0))).getItems().get(0).toString()
        				,(NonTerminal) ((Production)(((PriorityBlock)(node.getPriorityBlocks().
        						get(0))).getProductions().get(0))).getItems().get(0)
        						,node.getChild(null));
    			return result;
    		}
    	} else {
    		if(((Production)(((PriorityBlock)(node.getPriorityBlocks().
				get(0))).getProductions().get(0))).isListDecl()){
    			Production production = ((Production)(((PriorityBlock)(node.getPriorityBlocks().
    					get(0))).getProductions().get(0)));
                UserList userList = (UserList) production.getItems().get(0);
                String separator = "'_"+userList.getSeparator()+"_";
                String terminator = "."+userList.getSort().toString();
                NonTerminal contentType = new NonTerminal(userList.getSort());
                Set<Production> checkStrict = SyntaxByTag.get(node, STRICT, context);
                checkStrict.addAll(SyntaxByTag.get(node, SEQSTRICT, context));
                if(checkStrict.isEmpty()){
                	return new ListElement(separator,this.generateName(separator)
                    		,terminator,this.generateName(terminator),contentType,node.getChild(null),false);
                }
                return new ListElement(separator,this.generateName(separator)
                		,terminator,this.generateName(terminator),contentType,node.getChild(null),true);
    		}
    		
    		Production production = ((Production)(((PriorityBlock)(node.getPriorityBlocks().
    				get(0))).getProductions().get(0)));
    		List<NonTerminal> arguments = new ArrayList<NonTerminal>();
    		for(int i = 0; i < production.getItems().size(); ++i){
    			if(production.getItems().get(i) instanceof NonTerminal){
    				arguments.add((NonTerminal) production.getItems().get(i));
    			}
    		}

            Set<Production> checkStrict = SyntaxByTag.get(node, STRICT, context);
            checkStrict.addAll(SyntaxByTag.get(node, SEQSTRICT, context));
            List<Integer> strictnessPositions = new ArrayList<>();
            
            //do some checks on strictness rules.
            if(!checkStrict.isEmpty()){
            	if (!(production.getSort().isComputationSort()
                		|| production.getSort().equals(Sort.KLABEL))) {
                    throw KExceptionManager.compilerError(
                            "only productions of sort K, sort KLabel or of syntactic sorts can have "
                                    + "strictness attributes",
                            this, production);
                }

                if (production.isSubsort()) {
                    throw KExceptionManager.compilerError(
                            "Production is a subsort and cannot be strict.",
                            this, production);
                }

                if (production.isConstant() && !production.getSort().equals(Sort.KLABEL)) {
                    throw KExceptionManager.compilerError(
                            "Production is a constant and cannot be strict.",
                            this, production);
                }
                
                boolean isSeq = production.containsAttribute(SEQSTRICT);
                final String strictType;
                if (!isSeq) {
                    strictType = STRICT;
                } else {
                    strictType = SEQSTRICT;
                }
                
                String attribute = production.getAttribute(strictType);
                String[] strictAttrs = null;
                int arity = production.getArityOfKItem();
                
                if (attribute.isEmpty()) {
                    for (int i = 1; i <= arity; i++) {
                        strictnessPositions.add(i);
                    }
                } else {
                    strictAttrs = attribute.split(",");
                    for (String strictAttr : strictAttrs) {
                        try {
                            strictnessPositions.add(Integer.parseInt(strictAttr.trim()));
                        } catch (NumberFormatException e) {
                            throw KExceptionManager.compilerError(
                                    "Expecting a number between 1 and "
                            + arity + ", but found " + strictAttr + " as a" +
                                            " strict position in " + Arrays.toString(strictAttrs),
                                    this, production);
                        }
                    }
                }
            }
    		return new NormalElement(generateKLabel(production)
    				,generateName(generateKLabel(production))
    				,arguments,node.getChild(null),strictnessPositions);
    	}
    	return new ThePair();
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
    			} else if(aPair instanceof FunctionElement){
    				syntaxElement.addFunction(((FunctionElement)aPair));
    			} else if(aPair.getResultSort().getSort().equals(Sort.KRESULT)){
    				syntaxElement.addKResult(aPair);
    			} else {
    				syntaxElement.addSort(aPair.getResultSort(), aPair);
    				List<NonTerminal> subSorts = aPair.getSubSorts();
    				if(subSorts != null){
    					for(int index = 0; index < subSorts.size(); ++index){
    						syntaxElement.addToGraph(aPair.getResultSort(), subSorts.get(index));
    					}
    				}
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