package analysis;

import java.io.FileWriter;
import java.io.IOException;
import java.lang.annotation.Annotation;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Locale;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import spoon.reflect.CtModel;

import spoon.reflect.code.CtLambda;
import spoon.reflect.code.CtCatch;
import spoon.reflect.code.CtBlock;
import spoon.reflect.code.CtNewClass;
import spoon.reflect.reference.CtFieldReference;
import spoon.reflect.reference.CtLocalVariableReference;
import spoon.reflect.reference.CtParameterReference;
import spoon.reflect.reference.CtVariableReference;
import spoon.Launcher;
import spoon.reflect.code.CtAssignment;
import spoon.reflect.code.CtBinaryOperator;
import spoon.reflect.code.CtConditional;
import spoon.reflect.code.CtConstructorCall;
import spoon.reflect.code.CtExpression;
import spoon.reflect.code.CtFieldAccess;
import spoon.reflect.code.CtIf;
import spoon.reflect.code.CtInvocation;
import spoon.reflect.code.CtLiteral;
import spoon.reflect.code.CtLocalVariable;
import spoon.reflect.code.CtLoop;
import spoon.reflect.code.CtReturn;
import spoon.reflect.code.CtStatement;
import spoon.reflect.code.CtThisAccess;
import spoon.reflect.code.CtTry;
import spoon.reflect.code.CtTypeAccess;
import spoon.reflect.code.CtVariableRead;
import spoon.reflect.code.CtVariableWrite;
import spoon.reflect.cu.SourcePosition;
import spoon.reflect.declaration.CtAnnotation;
import spoon.reflect.declaration.CtExecutable;
import spoon.reflect.declaration.CtMethod;
import spoon.reflect.declaration.CtModifiable;
import spoon.reflect.declaration.CtPackage;
import spoon.reflect.declaration.CtType;
import spoon.reflect.reference.CtExecutableReference;
import spoon.reflect.reference.CtTypeReference;
import spoon.reflect.visitor.filter.TypeFilter;
import spoon.reflect.declaration.CtClass;

public class CallExtractor {

    private static final String PROJECT_ROOT = "org.springframework.samples.petclinic";

    public static void main(String[] args) {
        try (FileWriter writer = new FileWriter("calls.csv")) {

            writer.write(String.join(",",
                "Caller",
                "CallerSignature",
                "Callee",
                "CalleeSignature",
                "CalleeParameterTypes",
                "ReturnType",
                "IsVoidCall",
                "CallerPackage",
                "CallerLayer",
                "CalleeLayer",
                "LayerRelation",
                "IsInternal",
                "ResolutionQuality",
                "ArgCount",
                "HasLiteralArg",
                "HasNullArg",
                "HasBooleanArg",
                "HasNestedInvocationArg",
                "ArgumentStaticTypes",
                "Line",
                "StandaloneStatement",
                "ReturnUsed",
                "AssignedToVariable",
                "ReturnedDirectly",
                "PassedAsArgument",
                "InIfCondition",
                "InsideIfBody",
                "InsideLoop",
                "InLoopCondition",
                "InsideTry",
                "InsideCatch",
                "InsideFinally",
                "ThrowsHandledLocally",
                "InTernaryCondition",
                "InsideLambda",
                "InsideAnonymousClass",
                "ReceiverCategory",
                "ReceiverExpressionKind",
                "ReceiverType",
                "ReceiverOrigin",
                "InvocationMode",
                "MethodName",
                "NamePattern",
                "NameStartsWithGet",
                "NameStartsWithFind",
                "NameStartsWithSave",
                "NameStartsWithExists",
                "NameStartsWithDelete",
                "NameStartsWithUpdate",
                "NameStartsWithIs",
                "NameStartsWithHas",
                "NameContainsValidate",
                "NameContainsCheck",
                "BooleanLikeCall",
                "CallerMethodNamePattern",
                "CallerReturnType",
                "CallerClassRole",
                "CallerAnnotations",
                "CallerTransactional",
                "CallerTest",
                "CallerRequestHandler",
                "CallerOverride",
                "CalleeAritySignature",
                "ArgumentTypePattern",
                "DistanceInCallChain",
                "InternalResolutionQuality",
                "CalleeModifiers",
                "IsCollectionOperation"
            ));
            writer.write("\n");

            Launcher launcher = new Launcher();
            launcher.addInputResource("/Users/mmilushev/VisualStudioProjects/spring-petclinic-main");
            launcher.buildModel();

            CtModel model = launcher.getModel();

            int count = 0;

            for (CtInvocation<?> invocation : model.getElements(new TypeFilter<>(CtInvocation.class))) {
                CtMethod<?> callerMethod = invocation.getParent(CtMethod.class);
                if (callerMethod == null) {
                    continue;
                }

                CtType<?> callerType = callerMethod.getDeclaringType();
                if (callerType == null) {
                    continue;
                }

                count++;

                CtExecutableReference<?> executableRef = invocation.getExecutable();
                CtTypeReference<?> calleeDeclaringTypeRef =
                        executableRef != null ? executableRef.getDeclaringType() : null;

                String caller = callerType.getQualifiedName() + "#" + callerMethod.getSimpleName();

                String methodName = executableRef != null && executableRef.getSimpleName() != null
                        ? executableRef.getSimpleName()
                        : "UNKNOWN";

                String callee;
                if (calleeDeclaringTypeRef != null && methodName != null) {
                    callee = calleeDeclaringTypeRef.getQualifiedName() + "#" + methodName;
                } else if (methodName != null) {
                    callee = methodName;
                } else {
                    callee = "UNKNOWN";
                }

                String callerSignature = callerType.getQualifiedName() + "#" + callerMethod.getSignature();

                String calleeSignature = deriveCalleeSignature(executableRef);
                String calleeParameterTypes = deriveCalleeParameterTypes(executableRef);

                boolean isVoidCall = isVoidCall(invocation);

                String argumentStaticTypes = deriveArgumentStaticTypes(invocation);

                boolean insideCatch = isInsideCatch(invocation);
                boolean insideFinally = isInsideFinally(invocation);
                boolean insideLambda = invocation.getParent(CtLambda.class) != null;
                boolean insideAnonymousClass = invocation.getParent(CtNewClass.class) != null;

                String receiverType = deriveReceiverType(invocation);
                String receiverOrigin = deriveReceiverOrigin(invocation);
                String invocationMode = deriveInvocationMode(invocation);

                boolean callerTransactional = hasAnyAnnotation(callerMethod, callerType, "Transactional");
                boolean callerTest = hasAnyAnnotation(callerMethod, callerType, "Test", "ParameterizedTest", "RepeatedTest");
                boolean callerRequestHandler = hasAnyAnnotation(
                        callerMethod, callerType,
                        "RequestMapping", "GetMapping", "PostMapping", "PutMapping", "DeleteMapping", "PatchMapping"
                );
                boolean callerOverride = hasAnyMethodAnnotation(callerMethod, "Override");

                String returnType = invocation.getType() != null
                        ? safeQualifiedName(invocation.getType())
                        : "void";

                String callerPackage = "UNKNOWN";
                CtPackage callerPkg = callerType.getPackage();
                if (callerPkg != null) {
                    callerPackage = callerPkg.getQualifiedName();
                }

                String callerLayer = deriveLayer(callerPackage, callerType);
                String calleeLayer = deriveCalleeLayer(calleeDeclaringTypeRef);
                String layerRelation = callerLayer + "->" + calleeLayer;

                boolean isInternal = isInternalCallee(calleeDeclaringTypeRef);

                String resolutionQuality = deriveResolutionQuality(executableRef, calleeDeclaringTypeRef, isInternal);
                String internalResolutionQuality = deriveInternalResolutionQuality(calleeDeclaringTypeRef, isInternal);

                int argCount = invocation.getArguments().size();
                boolean hasLiteralArg = hasLiteralArg(invocation);
                boolean hasNullArg = hasNullArg(invocation);
                boolean hasBooleanArg = hasBooleanArg(invocation);
                boolean hasNestedInvocationArg = hasNestedInvocationArg(invocation);

                int line = extractLine(invocation);

                boolean standaloneStatement = isStandaloneStatement(invocation);
                boolean returnUsed = isReturnUsed(invocation);
                boolean assignedToVariable = isAssignedToVariable(invocation);
                boolean returnedDirectly = isReturnedDirectly(invocation);
                boolean passedAsArgument = isPassedAsArgument(invocation);

                boolean inIfCondition = isInIfCondition(invocation);
                boolean insideIfBody = isInsideIfBody(invocation);
                boolean insideLoop = invocation.getParent(CtLoop.class) != null;
                boolean inLoopCondition = isInLoopCondition(invocation);
                boolean insideTry = invocation.getParent(CtTry.class) != null;
                boolean throwsHandledLocally = isThrowsHandledLocally(invocation);
                boolean inTernaryCondition = isInTernaryCondition(invocation);

                String receiverCategory = deriveReceiverCategory(invocation);
                String receiverExpressionKind = deriveReceiverExpressionKind(invocation);

                String lowerMethodName = methodName.toLowerCase(Locale.ROOT);
                boolean nameStartsWithGet = lowerMethodName.startsWith("get");
                boolean nameStartsWithFind = lowerMethodName.startsWith("find");
                boolean nameStartsWithSave = lowerMethodName.startsWith("save");
                boolean nameStartsWithExists = lowerMethodName.startsWith("exists");
                boolean nameStartsWithDelete = lowerMethodName.startsWith("delete");
                boolean nameStartsWithUpdate = lowerMethodName.startsWith("update");
                boolean nameStartsWithIs = lowerMethodName.startsWith("is");
                boolean nameStartsWithHas = lowerMethodName.startsWith("has");
                boolean nameContainsValidate = lowerMethodName.contains("validate");
                boolean nameContainsCheck = lowerMethodName.contains("check");

                String namePattern = deriveNamePattern(lowerMethodName);
                boolean booleanLikeCall = isBooleanLikeCall(lowerMethodName, invocation.getType());

                String callerMethodNamePattern = deriveMethodPattern(callerMethod.getSimpleName());
                String callerReturnType = callerMethod.getType() != null
                        ? safeQualifiedName(callerMethod.getType())
                        : "void";

                String callerClassRole = deriveClassRole(callerType);
                String callerAnnotations = extractAnnotations(callerMethod, callerType);

                String calleeAritySignature = deriveAritySignature(argCount);
                String argumentTypePattern = deriveArgumentTypePattern(invocation);
                int distanceInCallChain = computeDistanceInCallChain(invocation);
                String calleeModifiers = extractCalleeModifiers(executableRef);
                boolean isCollectionOperation = isCollectionOperation(invocation, methodName);

                writer.write(String.join(",",
                    csv(caller),
                    csv(callerSignature),
                    csv(callee),
                    csv(calleeSignature),
                    csv(calleeParameterTypes),
                    csv(returnType),
                    String.valueOf(isVoidCall),
                    csv(callerPackage),
                    csv(callerLayer),
                    csv(calleeLayer),
                    csv(layerRelation),
                    String.valueOf(isInternal),
                    csv(resolutionQuality),
                    String.valueOf(argCount),
                    String.valueOf(hasLiteralArg),
                    String.valueOf(hasNullArg),
                    String.valueOf(hasBooleanArg),
                    String.valueOf(hasNestedInvocationArg),
                    csv(argumentStaticTypes),
                    String.valueOf(line),
                    String.valueOf(standaloneStatement),
                    String.valueOf(returnUsed),
                    String.valueOf(assignedToVariable),
                    String.valueOf(returnedDirectly),
                    String.valueOf(passedAsArgument),
                    String.valueOf(inIfCondition),
                    String.valueOf(insideIfBody),
                    String.valueOf(insideLoop),
                    String.valueOf(inLoopCondition),
                    String.valueOf(insideTry),
                    String.valueOf(insideCatch),
                    String.valueOf(insideFinally),
                    String.valueOf(throwsHandledLocally),
                    String.valueOf(inTernaryCondition),
                    String.valueOf(insideLambda),
                    String.valueOf(insideAnonymousClass),
                    csv(receiverCategory),
                    csv(receiverExpressionKind),
                    csv(receiverType),
                    csv(receiverOrigin),
                    csv(invocationMode),
                    csv(methodName),
                    csv(namePattern),
                    String.valueOf(nameStartsWithGet),
                    String.valueOf(nameStartsWithFind),
                    String.valueOf(nameStartsWithSave),
                    String.valueOf(nameStartsWithExists),
                    String.valueOf(nameStartsWithDelete),
                    String.valueOf(nameStartsWithUpdate),
                    String.valueOf(nameStartsWithIs),
                    String.valueOf(nameStartsWithHas),
                    String.valueOf(nameContainsValidate),
                    String.valueOf(nameContainsCheck),
                    String.valueOf(booleanLikeCall),
                    csv(callerMethodNamePattern),
                    csv(callerReturnType),
                    csv(callerClassRole),
                    csv(callerAnnotations),
                    String.valueOf(callerTransactional),
                    String.valueOf(callerTest),
                    String.valueOf(callerRequestHandler),
                    String.valueOf(callerOverride),
                    csv(calleeAritySignature),
                    csv(argumentTypePattern),
                    String.valueOf(distanceInCallChain),
                    csv(internalResolutionQuality),
                    csv(calleeModifiers),
                    String.valueOf(isCollectionOperation)
                ));
                writer.write("\n");
            }

            System.out.println("Total exported call sites: " + count);

        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private static String deriveCalleeSignature(CtExecutableReference<?> executableRef) {
        if (executableRef == null) {
            return "UNKNOWN";
        }

        String methodSig;
        try {
            methodSig = executableRef.getSignature(); // save(java.lang.String,int)
        } catch (Exception e) {
            methodSig = executableRef.getSimpleName() + "(" + deriveCalleeParameterTypes(executableRef) + ")";
        }

        CtTypeReference<?> declaringType = executableRef.getDeclaringType();
        if (declaringType != null) {
            return safeQualifiedName(declaringType) + "#" + methodSig;
        }

        return methodSig != null ? methodSig : "UNKNOWN";
    }

    private static String deriveArgumentStaticTypes(CtInvocation<?> invocation) {
        List<String> parts = new ArrayList<>();

        for (CtExpression<?> arg : invocation.getArguments()) {
            if (arg == null) {
                parts.add("UNKNOWN");
                continue;
            }

            if (arg instanceof CtLiteral<?>) {
                CtLiteral<?> lit = (CtLiteral<?>) arg;
                if (lit.getValue() == null) {
                    parts.add("NULL");
                    continue;
                }
            }

            CtTypeReference<?> type = arg.getType();
            parts.add(safeQualifiedName(type));
        }

        return parts.isEmpty() ? "NONE" : String.join("|", parts);
    }

    private static String deriveInvocationMode(CtInvocation<?> invocation) {
        CtExpression<?> target = invocation.getTarget();

        if (target == null) {
            return "IMPLICIT_THIS";
        }
        if (target instanceof CtTypeAccess<?>) {
            return "STATIC";
        }
        if (target instanceof CtInvocation<?>) {
            return "CHAINED";
        }
        if (target instanceof CtConstructorCall<?>) {
            return "CONSTRUCTOR_CHAIN";
        }
        return "INSTANCE";
    }

    private static boolean isVoidCall(CtInvocation<?> invocation) {
        CtTypeReference<?> type = invocation.getType();
        if (type == null) {
            return true;
        }

        String qn = safeQualifiedName(type);
        return "void".equals(qn);
    }
    
    private static boolean isInsideCatch(CtInvocation<?> invocation) {
        return invocation.getParent(CtCatch.class) != null;
    }

    private static boolean isInsideFinally(CtInvocation<?> invocation) {
        CtTry ctTry = invocation.getParent(CtTry.class);
        if (ctTry == null || ctTry.getFinalizer() == null) {
            return false;
        }

        CtBlock<?> finalizer = ctTry.getFinalizer();
        return invocation == finalizer || invocation.hasParent(finalizer);
    }

    private static boolean hasAnyAnnotation(CtMethod<?> method, CtType<?> type, String... names) {
        Set<String> present = new TreeSet<>();
        present.addAll(extractAnnotationSimpleNames(method.getAnnotations()));
        present.addAll(extractAnnotationSimpleNames(type.getAnnotations()));

        for (String name : names) {
            if (present.contains(name)) {
                return true;
            }
        }
        return false;
    }

    private static boolean hasAnyMethodAnnotation(CtMethod<?> method, String... names) {
        Set<String> present = extractAnnotationSimpleNames(method.getAnnotations());
        for (String name : names) {
            if (present.contains(name)) {
                return true;
            }
        }
        return false;
    }

    private static String deriveReceiverOrigin(CtInvocation<?> invocation) {
        CtExpression<?> target = invocation.getTarget();

        if (target == null) {
            return "THIS";
        }
        if (target instanceof CtThisAccess<?>) {
            return "THIS";
        }
        if (target instanceof CtTypeAccess<?>) {
            return "STATIC";
        }
        if (target instanceof CtInvocation<?>) {
            return "CHAINED";
        }
        if (target instanceof CtConstructorCall<?>) {
            return "CONSTRUCTOR_RESULT";
        }
        if (target instanceof CtFieldAccess<?>) {
            return "FIELD";
        }
        if (target instanceof CtVariableRead<?> || target instanceof CtVariableWrite<?>) {
            CtVariableReference<?> ref =
                    target instanceof CtVariableRead<?>
                            ? ((CtVariableRead<?>) target).getVariable()
                            : ((CtVariableWrite<?>) target).getVariable();

            if (ref instanceof CtFieldReference<?>) {
                return "FIELD";
            }
            if (ref instanceof CtParameterReference<?>) {
                return "PARAMETER";
            }
            if (ref instanceof CtLocalVariableReference<?>) {
                return "LOCAL";
            }
            return "VARIABLE";
        }

        return "UNKNOWN";
    }

    private static String deriveReceiverType(CtInvocation<?> invocation) {
        CtExpression<?> target = invocation.getTarget();
        if (target == null) {
            return "IMPLICIT_THIS";
        }

        CtTypeReference<?> type = target.getType();
        return safeQualifiedName(type);
    }

    private static String deriveCalleeParameterTypes(CtExecutableReference<?> executableRef) {
        if (executableRef == null || executableRef.getParameters() == null) {
            return "UNKNOWN";
        }

        List<String> parts = new ArrayList<>();
        for (CtTypeReference<?> paramType : executableRef.getParameters()) {
            parts.add(safeQualifiedName(paramType));
        }

        return parts.isEmpty() ? "NONE" : String.join("|", parts);
    }

    private static int extractLine(CtInvocation<?> invocation) {
        SourcePosition position = invocation.getPosition();
        if (position != null && position.isValidPosition()) {
            return position.getLine();
        }
        return -1;
    }

    private static boolean isInternalCallee(CtTypeReference<?> calleeType) {
        return calleeType != null
                && calleeType.getQualifiedName() != null
                && calleeType.getQualifiedName().startsWith(PROJECT_ROOT);
    }

    private static String deriveResolutionQuality(
            CtExecutableReference<?> executableRef,
            CtTypeReference<?> calleeType,
            boolean isInternal
    ) {
        if (executableRef == null) {
            return "NO_EXECUTABLE";
        }
        if (calleeType == null) {
            return "NO_DECLARING_TYPE";
        }
        if (safeQualifiedName(calleeType).equals("UNKNOWN")) {
            return "UNKNOWN_TYPE";
        }
        return isInternal ? "RESOLVED_INTERNAL" : "RESOLVED_EXTERNAL";
    }

    private static String deriveInternalResolutionQuality(CtTypeReference<?> calleeType, boolean isInternal) {
        if (calleeType == null) {
            return "UNRESOLVED";
        }
        if (!isInternal) {
            return "EXTERNAL";
        }
        return "INTERNAL_RESOLVED";
    }

    private static boolean hasLiteralArg(CtInvocation<?> invocation) {
        for (CtExpression<?> arg : invocation.getArguments()) {
            if (arg instanceof CtLiteral<?>) {
                return true;
            }
        }
        return false;
    }

    private static boolean hasBooleanArg(CtInvocation<?> invocation) {
        for (CtExpression<?> arg : invocation.getArguments()) {
            if (arg instanceof CtLiteral<?>) {
                CtLiteral<?> literal = (CtLiteral<?>) arg;
                if (literal.getValue() instanceof Boolean) {
                    return true;
                }
            }
        }
        return false;
    }

    private static boolean hasNullArg(CtInvocation<?> invocation) {
        for (CtExpression<?> arg : invocation.getArguments()) {
            if (arg instanceof CtLiteral<?>) {
                CtLiteral<?> literal = (CtLiteral<?>) arg;
                if (literal.getValue() == null) {
                    return true;
                }
            }
        }
        return false;
    }

    private static boolean hasNestedInvocationArg(CtInvocation<?> invocation) {
        for (CtExpression<?> arg : invocation.getArguments()) {
            if (arg instanceof CtInvocation<?> || arg.getElements(new TypeFilter<>(CtInvocation.class)).size() > 0) {
                return true;
            }
        }
        return false;
    }

    private static boolean isStandaloneStatement(CtInvocation<?> invocation) {
        CtStatement parentStatement = invocation.getParent(CtStatement.class);
        return parentStatement == invocation;
    }

    private static boolean isReturnUsed(CtInvocation<?> invocation) {
        return !isStandaloneStatement(invocation);
    }

    private static boolean isAssignedToVariable(CtInvocation<?> invocation) {
        CtLocalVariable<?> localVar = invocation.getParent(CtLocalVariable.class);
        if (localVar != null && localVar.getDefaultExpression() != null) {
            return invocation == localVar.getDefaultExpression()
                    || invocation.hasParent(localVar.getDefaultExpression());
        }

        CtAssignment<?, ?> assignment = invocation.getParent(CtAssignment.class);
        return assignment != null;
    }

    private static boolean isReturnedDirectly(CtInvocation<?> invocation) {
        CtReturn<?> ctReturn = invocation.getParent(CtReturn.class);
        if (ctReturn == null) {
            return false;
        }
        CtExpression<?> returned = ctReturn.getReturnedExpression();
        return returned != null && (returned == invocation || invocation.hasParent(returned));
    }

    private static boolean isPassedAsArgument(CtInvocation<?> invocation) {
        CtInvocation<?> parentInvocation = invocation.getParent(CtInvocation.class);
        if (parentInvocation != null && parentInvocation != invocation) {
            for (CtExpression<?> arg : parentInvocation.getArguments()) {
                if (arg == invocation || invocation.hasParent(arg)) {
                    return true;
                }
            }
        }

        CtConstructorCall<?> parentCtor = invocation.getParent(CtConstructorCall.class);
        if (parentCtor != null) {
            for (CtExpression<?> arg : parentCtor.getArguments()) {
                if (arg == invocation || invocation.hasParent(arg)) {
                    return true;
                }
            }
        }

        return false;
    }

    private static boolean isInIfCondition(CtInvocation<?> invocation) {
        CtIf ctIf = invocation.getParent(CtIf.class);
        if (ctIf == null || ctIf.getCondition() == null) {
            return false;
        }
        return invocation == ctIf.getCondition() || invocation.hasParent(ctIf.getCondition());
    }

    private static boolean isInsideIfBody(CtInvocation<?> invocation) {
        CtIf ctIf = invocation.getParent(CtIf.class);
        if (ctIf == null) {
            return false;
        }

        CtStatement thenStmt = ctIf.getThenStatement();
        CtStatement elseStmt = ctIf.getElseStatement();

        boolean inThen = thenStmt != null && (invocation == thenStmt || invocation.hasParent(thenStmt));
        boolean inElse = elseStmt != null && (invocation == elseStmt || invocation.hasParent(elseStmt));

        return (inThen || inElse) && !isInIfCondition(invocation);
    }

    private static boolean isInLoopCondition(CtInvocation<?> invocation) {
        try {
            Method getLoopingExpression = CtLoop.class.getMethod("getLoopingExpression");
            CtLoop loop = invocation.getParent(CtLoop.class);
            if (loop == null) {
                return false;
            }
            Object expr = getLoopingExpression.invoke(loop);
            if (expr instanceof CtExpression<?>) {
                CtExpression<?> condition = (CtExpression<?>) expr;
                return invocation == condition || invocation.hasParent(condition);
            }
        } catch (Exception ignored) {
            // Spoon versions differ here. Ignore and fall back.
        }

        CtBinaryOperator<?> binary = invocation.getParent(CtBinaryOperator.class);
        CtLoop loop = invocation.getParent(CtLoop.class);
        return loop != null && binary != null && invocation.hasParent(binary);
    }

    private static boolean isThrowsHandledLocally(CtInvocation<?> invocation) {
        CtTry ctTry = invocation.getParent(CtTry.class);
        return ctTry != null && ctTry.getCatchers() != null && !ctTry.getCatchers().isEmpty();
    }

    private static boolean isInTernaryCondition(CtInvocation<?> invocation) {
        CtConditional<?> conditional = invocation.getParent(CtConditional.class);
        if (conditional == null || conditional.getCondition() == null) {
            return false;
        }
        return invocation == conditional.getCondition() || invocation.hasParent(conditional.getCondition());
    }

    private static String deriveReceiverCategory(CtInvocation<?> invocation) {
        CtExpression<?> target = invocation.getTarget();
        if (target == null) {
            return "implicit";
        }

        CtTypeReference<?> typeRef = target.getType();
        String typeName = typeRef != null ? safeQualifiedName(typeRef).toLowerCase(Locale.ROOT) : "";

        if (typeName.contains("logger") || typeName.contains("log")) {
            return "logger";
        }
        if (typeName.contains("repository") || typeName.contains("repo")) {
            return "repository";
        }
        if (typeName.contains("service")) {
            return "service";
        }
        if (typeName.contains("controller")) {
            return "controller";
        }
        if (typeName.contains("collection")
                || typeName.contains("list")
                || typeName.contains("set")
                || typeName.contains("map")
                || typeName.contains("queue")) {
            return "collection";
        }
        if (typeName.contains("stream")) {
            return "stream";
        }
        if (typeName.contains("optional")) {
            return "optional";
        }
        if (typeName.startsWith(PROJECT_ROOT.toLowerCase(Locale.ROOT))) {
            return "domain_or_internal";
        }

        if (target instanceof CtThisAccess<?>) {
            return "this";
        }
        if (target instanceof CtFieldAccess<?>) {
            return "field";
        }
        if (target instanceof CtVariableRead<?> || target instanceof CtVariableWrite<?>) {
            return "variable";
        }
        if (target instanceof CtTypeAccess<?>) {
            return "static_type";
        }
        if (target instanceof CtInvocation<?>) {
            return "chained_call";
        }
        if (target instanceof CtConstructorCall<?>) {
            return "constructor_result";
        }

        return "other";
    }

    private static String deriveReceiverExpressionKind(CtInvocation<?> invocation) {
        CtExpression<?> target = invocation.getTarget();
        if (target == null) {
            return "IMPLICIT";
        }
        if (target instanceof CtThisAccess<?>) {
            return "THIS";
        }
        if (target instanceof CtFieldAccess<?>) {
            return "FIELD_ACCESS";
        }
        if (target instanceof CtVariableRead<?> || target instanceof CtVariableWrite<?>) {
            return "VARIABLE";
        }
        if (target instanceof CtTypeAccess<?>) {
            return "TYPE_ACCESS";
        }
        if (target instanceof CtInvocation<?>) {
            return "CHAINED_INVOCATION";
        }
        if (target instanceof CtConstructorCall<?>) {
            return "CONSTRUCTOR_RESULT";
        }
        return target.getClass().getSimpleName();
    }

    private static String deriveNamePattern(String lowerMethodName) {
        if (lowerMethodName == null || lowerMethodName.isBlank()) {
            return "unknown";
        }

        if (lowerMethodName.startsWith("get")
                || lowerMethodName.startsWith("find")
                || lowerMethodName.startsWith("fetch")
                || lowerMethodName.startsWith("load")
                || lowerMethodName.startsWith("read")) {
            return "query";
        }

        if (lowerMethodName.startsWith("save")
                || lowerMethodName.startsWith("delete")
                || lowerMethodName.startsWith("update")
                || lowerMethodName.startsWith("remove")
                || lowerMethodName.startsWith("set")
                || lowerMethodName.startsWith("create")
                || lowerMethodName.startsWith("add")) {
            return "command";
        }

        if (lowerMethodName.startsWith("is")
                || lowerMethodName.startsWith("has")
                || lowerMethodName.startsWith("exists")
                || lowerMethodName.contains("check")
                || lowerMethodName.contains("validate")) {
            return "guard";
        }

        if (lowerMethodName.startsWith("process")
                || lowerMethodName.startsWith("handle")
                || lowerMethodName.startsWith("execute")) {
            return "orchestration";
        }

        return "other";
    }

    private static boolean isBooleanLikeCall(String lowerMethodName, CtTypeReference<?> typeRef) {
        if (lowerMethodName.startsWith("is")
                || lowerMethodName.startsWith("has")
                || lowerMethodName.startsWith("exists")
                || lowerMethodName.startsWith("can")
                || lowerMethodName.startsWith("should")) {
            return true;
        }

        if (typeRef == null) {
            return false;
        }

        String qn = safeQualifiedName(typeRef);
        return "boolean".equals(qn) || "java.lang.Boolean".equals(qn);
    }

    private static String deriveMethodPattern(String methodName) {
        if (methodName == null) {
            return "unknown";
        }

        String lower = methodName.toLowerCase(Locale.ROOT);

        if (lower.startsWith("get")
                || lower.startsWith("find")
                || lower.startsWith("list")
                || lower.startsWith("load")
                || lower.startsWith("fetch")) {
            return "query";
        }

        if (lower.startsWith("save")
                || lower.startsWith("create")
                || lower.startsWith("update")
                || lower.startsWith("delete")
                || lower.startsWith("remove")
                || lower.startsWith("set")) {
            return "command";
        }

        if (lower.startsWith("validate")
                || lower.startsWith("check")
                || lower.startsWith("verify")
                || lower.startsWith("assert")) {
            return "guard";
        }

        if (lower.startsWith("process")
                || lower.startsWith("handle")
                || lower.startsWith("execute")
                || lower.startsWith("run")) {
            return "orchestration";
        }

        return "other";
    }

    private static String deriveClassRole(CtType<?> callerType) {
        String annotationRole = deriveAnnotationRole(callerType);
        if (!"unknown".equals(annotationRole)) {
            return annotationRole;
        }

        String typeName = callerType.getQualifiedName().toLowerCase(Locale.ROOT);
        if (typeName.contains(".controller") || typeName.endsWith("controller")) {
            return "controller";
        }
        if (typeName.contains(".service") || typeName.endsWith("service")) {
            return "service";
        }
        if (typeName.contains(".repository") || typeName.endsWith("repository")) {
            return "repository";
        }
        if (typeName.contains(".model") || typeName.contains(".domain")) {
            return "domain";
        }
        return "other";
    }

    private static String deriveAnnotationRole(CtType<?> callerType) {
        Set<String> names = extractAnnotationSimpleNames(callerType.getAnnotations());

        if (names.contains("RestController") || names.contains("Controller")) {
            return "controller";
        }
        if (names.contains("Service")) {
            return "service";
        }
        if (names.contains("Repository")) {
            return "repository";
        }
        if (names.contains("Component")) {
            return "component";
        }
        return "unknown";
    }

    private static String extractAnnotations(CtMethod<?> method, CtType<?> type) {
        Set<String> names = new TreeSet<>();

        names.addAll(extractAnnotationSimpleNames(method.getAnnotations()));
        names.addAll(extractAnnotationSimpleNames(type.getAnnotations()));

        if (names.isEmpty()) {
            return "NONE";
        }

        return String.join("|", names);
    }

    private static Set<String> extractAnnotationSimpleNames(Collection<? extends CtAnnotation<? extends Annotation>> annotations) {
        Set<String> names = new TreeSet<>();
        for (CtAnnotation<?> annotation : annotations) {
            if (annotation.getAnnotationType() != null) {
                names.add(annotation.getAnnotationType().getSimpleName());
            }
        }
        return names;
    }

    private static String deriveAritySignature(int argCount) {
        if (argCount == 0) {
            return "ZERO";
        }
        if (argCount == 1) {
            return "ONE";
        }
        if (argCount == 2) {
            return "TWO";
        }
        if (argCount == 3) {
            return "THREE";
        }
        return "MANY";
    }

    private static String deriveArgumentTypePattern(CtInvocation<?> invocation) {
        List<String> parts = new ArrayList<>();

        for (CtExpression<?> arg : invocation.getArguments()) {
            if (arg instanceof CtLiteral<?>) {
                CtLiteral<?> literal = (CtLiteral<?>) arg;
                Object value = literal.getValue();
                if (value == null) {
                    parts.add("NULL");
                } else if (value instanceof Boolean) {
                    parts.add("BOOLEAN_LITERAL");
                } else if (value instanceof Number) {
                    parts.add("NUMBER_LITERAL");
                } else if (value instanceof String) {
                    parts.add("STRING_LITERAL");
                } else {
                    parts.add("LITERAL");
                }
            } else if (arg instanceof CtInvocation<?>) {
                parts.add("INVOCATION");
            } else if (arg instanceof CtConstructorCall<?>) {
                parts.add("CONSTRUCTOR");
            } else if (arg instanceof CtVariableRead<?> || arg instanceof CtVariableWrite<?>) {
                parts.add("VARIABLE");
            } else if (arg instanceof CtFieldAccess<?>) {
                parts.add("FIELD");
            } else if (arg instanceof CtBinaryOperator<?>) {
                parts.add("BINARY");
            } else if (arg instanceof CtThisAccess<?>) {
                parts.add("THIS");
            } else {
                parts.add(arg.getClass().getSimpleName());
            }
        }

        if (parts.isEmpty()) {
            return "NONE";
        }

        return String.join("|", parts);
    }

    private static int computeDistanceInCallChain(CtInvocation<?> invocation) {
        int distance = 0;
        CtExpression<?> current = invocation.getTarget();

        while (current instanceof CtInvocation<?>) {
            CtInvocation<?> parentInvocation = (CtInvocation<?>) current;
            distance++;
            current = parentInvocation.getTarget();
        }

        return distance;
    }

    private static String extractCalleeModifiers(CtExecutableReference<?> executableRef) {
        if (executableRef == null) {
            return "UNKNOWN";
        }

        Set<String> modifiers = new TreeSet<String>();

        try {
            CtExecutable<?> decl = executableRef.getDeclaration();
            if (decl instanceof CtModifiable) {
                CtModifiable modifiable = (CtModifiable) decl;
                modifiable.getModifiers().forEach(m -> modifiers.add(m.name()));
            }
        } catch (Exception ignored) {

        }

        if (modifiers.isEmpty()) {
            return "UNKNOWN";
        }

        return String.join("|", modifiers);
    }

    private static boolean isCollectionOperation(CtInvocation<?> invocation, String methodName) {
        String lowerName = methodName == null ? "" : methodName.toLowerCase(Locale.ROOT);

        boolean methodLooksCollectionLike =
                lowerName.equals("add")
                        || lowerName.equals("remove")
                        || lowerName.equals("contains")
                        || lowerName.equals("put")
                        || lowerName.equals("get")
                        || lowerName.equals("size")
                        || lowerName.equals("clear")
                        || lowerName.equals("stream")
                        || lowerName.equals("map")
                        || lowerName.equals("filter")
                        || lowerName.equals("forEach".toLowerCase(Locale.ROOT));

        CtExpression<?> target = invocation.getTarget();
        if (target == null || target.getType() == null) {
            return methodLooksCollectionLike;
        }

        String typeName = safeQualifiedName(target.getType()).toLowerCase(Locale.ROOT);

        boolean receiverLooksCollectionLike =
                typeName.contains("collection")
                        || typeName.contains("list")
                        || typeName.contains("set")
                        || typeName.contains("map")
                        || typeName.contains("queue")
                        || typeName.contains("stream")
                        || typeName.contains("iterable");

        return methodLooksCollectionLike && receiverLooksCollectionLike;
    }

    private static String deriveLayer(String packageName, CtType<?> type) {
        String annotationRole = deriveAnnotationRole(type);
        if (!"unknown".equals(annotationRole)) {
            return annotationRole;
        }

        String lower = packageName == null ? "" : packageName.toLowerCase(Locale.ROOT);

        if (lower.contains(".controller")) {
            return "controller";
        }
        if (lower.contains(".service")) {
            return "service";
        }
        if (lower.contains(".repository") || lower.contains(".dao")) {
            return "repository";
        }
        if (lower.contains(".model") || lower.contains(".domain")) {
            return "domain";
        }
        if (lower.contains(".util") || lower.contains(".utils")) {
            return "util";
        }

        return "other";
    }

    private static String deriveCalleeLayer(CtTypeReference<?> calleeTypeRef) {
        if (calleeTypeRef == null) {
            return "unknown";
        }

        String qn = safeQualifiedName(calleeTypeRef);
        if ("UNKNOWN".equals(qn)) {
            return "unknown";
        }

        if (!qn.startsWith(PROJECT_ROOT)) {
            return "external";
        }

        String lower = qn.toLowerCase(Locale.ROOT);

        if (lower.contains(".controller.") || lower.endsWith(".controller")) {
            return "controller";
        }
        if (lower.contains(".service.") || lower.endsWith(".service")) {
            return "service";
        }
        if (lower.contains(".repository.") || lower.endsWith(".repository") || lower.contains(".dao.")) {
            return "repository";
        }
        if (lower.contains(".model.") || lower.contains(".domain.")) {
            return "domain";
        }
        if (lower.contains(".util.") || lower.contains(".utils.")) {
            return "util";
        }

        return "other";
    }

    private static String safeQualifiedName(CtTypeReference<?> typeRef) {
        if (typeRef == null) {
            return "UNKNOWN";
        }
        try {
            String qn = typeRef.getQualifiedName();
            return qn != null ? qn : "UNKNOWN";
        } catch (Exception e) {
            return "UNKNOWN";
        }
    }

    private static String csv(String value) {
        if (value == null) {
            return "";
        }
        if (value.contains(",") || value.contains("\"") || value.contains("\n")) {
            return "\"" + value.replace("\"", "\"\"") + "\"";
        }
        return value;
    }
}

/*
package analysis;

import java.io.FileWriter;
import java.io.IOException;

import spoon.Launcher;
import spoon.reflect.CtModel;
import spoon.reflect.code.CtInvocation;
import spoon.reflect.cu.SourcePosition;
import spoon.reflect.declaration.CtMethod;
import spoon.reflect.declaration.CtPackage;
import spoon.reflect.declaration.CtType;
import spoon.reflect.visitor.filter.TypeFilter;

public class CallExtractor {

    public static void main(String[] args) {
        try (FileWriter writer = new FileWriter("calls.csv")) {

            writer.write("Caller,Callee,ReturnType,Package,IsInternal,ArgCount,Line\n");

            Launcher launcher = new Launcher();
            launcher.addInputResource("/Users/mmilushev/VisualStudioProjects/spring-petclinic-main");
            launcher.buildModel();

            CtModel model = launcher.getModel();

            int count = 0;

            for (CtInvocation<?> invocation : model.getElements(new TypeFilter<>(CtInvocation.class))) {

                CtMethod<?> caller = invocation.getParent(CtMethod.class);
                if (caller == null) {
                    continue;
                }

                CtType<?> declaringType = caller.getDeclaringType();
                if (declaringType == null) {
                    continue;
                }

                count++;

                String callerName =
                        declaringType.getQualifiedName() + "#" + caller.getSimpleName();

                String callee = "UNKNOWN";
                if (invocation.getExecutable() != null &&
                    invocation.getExecutable().getDeclaringType() != null) {

                    callee =
                            invocation.getExecutable().getDeclaringType().getQualifiedName()
                            + "#"
                            + invocation.getExecutable().getSimpleName();
                }

                String returnType = "void";
                if (invocation.getType() != null) {
                    returnType = invocation.getType().getQualifiedName();
                }

                String packageName = "UNKNOWN";
                CtPackage pkg = declaringType.getPackage();
                if (pkg != null) {
                    packageName = pkg.getQualifiedName();
                }

                int line = -1;
                SourcePosition position = invocation.getPosition();
                if (position != null && position.isValidPosition()) {
                    line = position.getLine();
                }

                boolean internal = false;
                if (invocation.getExecutable() != null &&
                    invocation.getExecutable().getDeclaringType() != null) {
                    String calleeType = invocation.getExecutable().getDeclaringType().getQualifiedName();
                    //non-hardcoded version
                    //internal = calleeType.startsWith(declaringType.getPackage().getQualifiedName().split("\\.")[0]);
                    internal = calleeType.startsWith("org.springframework.samples.petclinic");
                }

                int argCount = invocation.getArguments().size();

                writer.write(
                        escapeCsv(callerName) + "," +
                        escapeCsv(callee) + "," +
                        escapeCsv(returnType) + "," +
                        escapeCsv(packageName) + "," +
                        internal + "," +
                        argCount + "," +
                        line + "\n"
                );
            }

            System.out.println("Total calls found: " + count);

        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private static String escapeCsv(String value) {
        if (value == null) {
            return "";
        }
        if (value.contains(",") || value.contains("\"") || value.contains("\n")) {
            return "\"" + value.replace("\"", "\"\"") + "\"";
        }
        return value;
    }
}
*/