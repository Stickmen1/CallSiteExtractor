package analysis;

import java.io.FileWriter;
import java.io.IOException;
import java.lang.annotation.Annotation;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

import spoon.Launcher;
import spoon.reflect.CtModel;
import spoon.reflect.code.BinaryOperatorKind;
import spoon.reflect.code.CtAssignment;
import spoon.reflect.code.CtBinaryOperator;
import spoon.reflect.code.CtBlock;
import spoon.reflect.code.CtCatch;
import spoon.reflect.code.CtConditional;
import spoon.reflect.code.CtConstructorCall;
import spoon.reflect.code.CtContinue;
import spoon.reflect.code.CtExpression;
import spoon.reflect.code.CtFieldAccess;
import spoon.reflect.code.CtIf;
import spoon.reflect.code.CtInvocation;
import spoon.reflect.code.CtLambda;
import spoon.reflect.code.CtLiteral;
import spoon.reflect.code.CtLocalVariable;
import spoon.reflect.code.CtLoop;
import spoon.reflect.code.CtNewClass;
import spoon.reflect.code.CtReturn;
import spoon.reflect.code.CtStatement;
import spoon.reflect.code.CtThisAccess;
import spoon.reflect.code.CtThrow;
import spoon.reflect.code.CtTry;
import spoon.reflect.code.CtTypeAccess;
import spoon.reflect.code.CtUnaryOperator;
import spoon.reflect.code.CtVariableRead;
import spoon.reflect.code.CtVariableWrite;
import spoon.reflect.cu.SourcePosition;
import spoon.reflect.declaration.CtAnnotation;
import spoon.reflect.declaration.CtElement;
import spoon.reflect.declaration.CtExecutable;
import spoon.reflect.declaration.CtMethod;
import spoon.reflect.declaration.CtModifiable;
import spoon.reflect.declaration.CtPackage;
import spoon.reflect.declaration.CtType;
import spoon.reflect.declaration.ModifierKind;
import spoon.reflect.reference.CtExecutableReference;
import spoon.reflect.reference.CtFieldReference;
import spoon.reflect.reference.CtLocalVariableReference;
import spoon.reflect.reference.CtParameterReference;
import spoon.reflect.reference.CtTypeReference;
import spoon.reflect.reference.CtVariableReference;
import spoon.reflect.visitor.filter.TypeFilter;

public class CallExtractorRevised {

    private static final String PROJECT_ROOT = "org.springframework.samples.petclinic";
    private static final String INPUT_RESOURCE = "/Users/mmilushev/VisualStudioProjects/spring-petclinic-main";

    public static void main(String[] args) {
        try (FileWriter writer = new FileWriter("calls.csv")) {
            writeHeader(writer);

            Launcher launcher = new Launcher();
            launcher.addInputResource(INPUT_RESOURCE);
            launcher.buildModel();

            CtModel model = launcher.getModel();

            List<CtInvocation<?>> invocations = model.getElements(new TypeFilter<>(CtInvocation.class))
                    .stream()
                    .filter(inv -> inv.getParent(CtMethod.class) != null)
                    .filter(inv -> {
                        CtMethod<?> m = inv.getParent(CtMethod.class);
                        return m.getDeclaringType() != null;
                    })
                    .collect(Collectors.toList());

            GraphStats graphStats = buildGraphStats(invocations);
            MethodSummary methodSummary = buildMethodSummary(invocations);

            int count = 0;

            for (CtInvocation<?> invocation : invocations) {
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
                CtTypeReference<?> calleeDeclaringTypeRef = executableRef != null ? executableRef.getDeclaringType() : null;

                String callerClassName = callerType.getQualifiedName();
                String caller = callerClassName + "#" + callerMethod.getSimpleName();
                String callerSignature = callerClassName + "#" + callerMethod.getSignature();

                String methodName = executableRef != null && executableRef.getSimpleName() != null
                        ? executableRef.getSimpleName()
                        : "UNKNOWN";

                String calleeClassName = calleeDeclaringTypeRef != null
                        ? safeQualifiedName(calleeDeclaringTypeRef)
                        : "UNKNOWN";

                String callee = calleeDeclaringTypeRef != null && methodName != null
                        ? calleeClassName + "#" + methodName
                        : (methodName != null ? methodName : "UNKNOWN");

                String calleeSignature = deriveCalleeSignature(executableRef);
                String calleeParameterTypes = deriveCalleeParameterTypes(executableRef);

                String returnType = invocation.getType() != null
                        ? safeQualifiedName(invocation.getType())
                        : "void";

                boolean isVoidCall = isVoidCall(invocation);

                String callerPackage = "UNKNOWN";
                CtPackage callerPkg = callerType.getPackage();
                if (callerPkg != null) {
                    callerPackage = callerPkg.getQualifiedName();
                }

                String callerLayer = deriveLayer(callerPackage, callerType);
                String calleeLayer = deriveCalleeLayer(calleeDeclaringTypeRef);
                String layerRelation = callerLayer + "->" + calleeLayer;
                boolean crossLayerCall = !"unknown".equals(calleeLayer)
                        && !"external".equals(calleeLayer)
                        && !callerLayer.equals(calleeLayer);

                boolean isInternal = isInternalCallee(calleeDeclaringTypeRef);
                String resolutionQuality = deriveResolutionQuality(executableRef, calleeDeclaringTypeRef, isInternal);
                String internalResolutionQuality = deriveInternalResolutionQuality(calleeDeclaringTypeRef, isInternal);

                int argCount = invocation.getArguments().size();
                String argumentStaticTypes = deriveArgumentStaticTypes(invocation);
                String argumentTypePattern = deriveArgumentTypePattern(invocation);
                String argumentOrigins = deriveArgumentOrigins(invocation);

                boolean hasLiteralArg = hasLiteralArg(invocation);
                boolean hasNullArg = hasNullArg(invocation);
                boolean hasBooleanArg = hasBooleanArg(invocation);
                boolean hasNestedInvocationArg = hasNestedInvocationArg(invocation);

                boolean insideCatch = isInsideCatch(invocation);
                boolean insideFinally = isInsideFinally(invocation);
                boolean insideLambda = invocation.getParent(CtLambda.class) != null;
                boolean insideAnonymousClass = invocation.getParent(CtNewClass.class) != null;

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

                int line = extractLine(invocation);
                int distanceInCallChain = computeDistanceInCallChain(invocation);

                String receiverCategory = deriveReceiverCategory(invocation);
                String receiverExpressionKind = deriveReceiverExpressionKind(invocation);
                String receiverType = deriveReceiverType(invocation);
                String receiverOrigin = deriveReceiverOrigin(invocation);
                String invocationMode = deriveInvocationMode(invocation);

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
                boolean booleanLikeCall = isBooleanLikeCall(lowerMethodName, invocation.getType());
                String namePattern = deriveNamePattern(lowerMethodName);

                boolean nameStartsWithNotify = startsWithAny(methodName, "notify");
                boolean nameStartsWithPublish = startsWithAny(methodName, "publish");
                boolean nameStartsWithEmit = startsWithAny(methodName, "emit");
                boolean nameStartsWithDispatch = startsWithAny(methodName, "dispatch");
                boolean nameStartsWithFire = startsWithAny(methodName, "fire");
                boolean nameStartsWithSend = startsWithAny(methodName, "send");
                boolean methodNameStartsWithCreate = startsWithAny(methodName, "create");
                boolean methodNameStartsWithBuild = startsWithAny(methodName, "build");
                boolean methodNameStartsWithOf = startsWithAny(methodName, "of");
                boolean methodNameStartsWithFrom = startsWithAny(methodName, "from");

                String callerMethodNamePattern = deriveMethodPattern(callerMethod.getSimpleName());
                String callerReturnType = callerMethod.getType() != null
                        ? safeQualifiedName(callerMethod.getType())
                        : "void";
                String callerClassRole = deriveClassRole(callerType);
                String callerAnnotations = extractAnnotations(callerMethod, callerType);

                boolean callerTransactional = hasAnyAnnotation(callerMethod, callerType, "Transactional");
                boolean callerTest = hasAnyAnnotation(callerMethod, callerType, "Test", "ParameterizedTest", "RepeatedTest");
                boolean callerRequestHandler = hasAnyAnnotation(
                        callerMethod, callerType,
                        "RequestMapping", "GetMapping", "PostMapping", "PutMapping", "DeleteMapping", "PatchMapping"
                );
                boolean callerOverride = hasAnyMethodAnnotation(callerMethod, "Override");

                String calleeAritySignature = deriveAritySignature(argCount);
                String calleeModifiers = extractCalleeModifiers(executableRef);
                boolean isCollectionOperation = isCollectionOperation(invocation, methodName);

                int callerMethodFanOut = graphStats.methodFanOut(callerSignature);
                int callerClassFanOut = graphStats.classFanOut(callerClassName);
                int calleeMethodFanIn = graphStats.methodFanIn(calleeSignature);
                int calleeClassFanIn = graphStats.classFanIn(calleeClassName);
                double callerMethodOutDegreeCentrality = graphStats.methodOutDegreeCentrality(callerSignature);
                double callerClassOutDegreeCentrality = graphStats.classOutDegreeCentrality(callerClassName);
                double calleeMethodInDegreeCentrality = graphStats.methodInDegreeCentrality(calleeSignature);
                double calleeClassInDegreeCentrality = graphStats.classInDegreeCentrality(calleeClassName);

                GuardFeatures guard = deriveGuardFeatures(invocation);
                ReceiverTypeFlags receiverFlags = deriveReceiverTypeFlags(invocation);
                ArgumentTypeFlags argumentFlags = deriveArgumentTypeFlags(invocation);

                boolean calleeDeclarationResolvable = isCalleeDeclarationResolvable(executableRef);
                boolean calleeTypeResolvable = isResolvable(calleeDeclaringTypeRef);
                boolean receiverTypeResolvable = isReceiverTypeResolvable(invocation);
                boolean allArgumentTypesResolvable = argumentFlags.allArgumentTypesResolvable;
                boolean anyArgumentTypeUnknown = argumentFlags.anyArgumentTypeUnknown;
                boolean hasKnownReturnType = invocation.getType() != null
                        && !"UNKNOWN".equals(safeQualifiedName(invocation.getType()));

                boolean receiverLooksLikeObserverPublisher = receiverLooksLike(invocation, "publisher", "observer", "multicaster", "notifier");
                boolean receiverLooksLikeEventBus = receiverLooksLike(invocation, "eventbus", "eventpublisher", "applicationeventpublisher", "bus");
                boolean receiverLooksLikeListenerRegistry = receiverLooksLike(invocation, "listener", "registry", "subscriber");
                boolean anyArgumentLooksLikeEvent = anyArgumentTypeNameContains(invocation, "event");
                boolean anyArgumentLooksLikeMessage = anyArgumentTypeNameContains(invocation, "message", "payload", "notification");
                boolean anyArgumentLooksLikeListener = anyArgumentTypeNameContains(invocation, "listener", "subscriber", "observer");
                boolean insideTransactionCallback = isInsideTransactionCallback(invocation);
                boolean followsStateMutationNearby = followsStateMutationNearby(invocation);

                boolean callerContainsMultipleDistinctCallees = methodSummary.distinctCalleesByMethod
                        .getOrDefault(callerSignature, Collections.emptySet()).size() > 1;
                int siblingInvocationCountInMethod = methodSummary.invocationCountByMethod
                        .getOrDefault(callerSignature, 0);
                boolean callsDependencyField = "FIELD".equals(deriveReceiverOrigin(invocation));
                boolean callsDifferentProjectComponentType = isInternalCallee(calleeDeclaringTypeRef)
                        && !normalizeRole(deriveClassRole(callerType)).equals(normalizeRole(calleeLayer));
                boolean insideDelegationChain = isPassedAsArgument(invocation)
                        || isReturnedDirectly(invocation)
                        || isPassedToAnotherInvocation(invocation);
                boolean hasChainedOrNestedDelegation = "CHAINED".equals(deriveInvocationMode(invocation))
                        || hasNestedInvocationArg(invocation)
                        || isPassedToAnotherInvocation(invocation);

                boolean returnValueIgnored = !isVoidCall(invocation) && isStandaloneStatement(invocation);
                boolean returnsBoolean = returnsBoolean(invocation);
                boolean returnsCollection = returnsCollection(invocation);
                boolean returnsOptional = returnsOptional(invocation);
                boolean returnsProjectType = returnsProjectType(invocation);
                boolean returnsExternalType = returnsExternalType(invocation);
                boolean methodLooksAccessor = methodLooksAccessor(methodName, invocation.getType());
                boolean methodLooksMutator = methodLooksMutator(methodName, invocation.getType());

                boolean callerLooksQueryMethod = looksLikeQueryMethod(callerMethod.getSimpleName(), callerMethod.getType(), callerMethod, callerType);
                boolean callerLooksCommandMethod = looksLikeCommandMethod(callerMethod.getSimpleName(), callerMethod.getType(), callerMethod, callerType);
                boolean callerLooksControllerMethod = looksLikeControllerMethod(callerMethod, callerType);
                boolean callerLooksFactoryMethod = looksLikeFactoryMethod(callerMethod.getSimpleName(), callerMethod.getType());
                boolean callerLooksValidatorMethod = looksLikeValidatorMethod(callerMethod.getSimpleName(), callerMethod.getType());
                boolean calleeLooksQueryMethod = looksLikeQueryMethod(methodName, invocation.getType(), null, null);
                boolean calleeLooksCommandMethod = looksLikeCommandMethod(methodName, invocation.getType(), null, null);
                boolean calleeLooksValidatorMethod = looksLikeValidatorMethod(methodName, invocation.getType());
                boolean calleeLooksFactoryMethod = looksLikeFactoryMethod(methodName, invocation.getType());
                boolean calleeLooksControllerMethod = "controller".equals(calleeLayer);

                boolean callerIsPublic = hasModifier(callerMethod, ModifierKind.PUBLIC);
                boolean callerIsPrivate = hasModifier(callerMethod, ModifierKind.PRIVATE);
                boolean callerIsProtected = hasModifier(callerMethod, ModifierKind.PROTECTED);
                boolean callerIsStatic = hasModifier(callerMethod, ModifierKind.STATIC);
                boolean callerIsAbstract = hasModifier(callerMethod, ModifierKind.ABSTRACT);
                boolean calleeIsStatic = calleeHasModifier(executableRef, ModifierKind.STATIC);
                boolean calleeIsAbstract = calleeHasModifier(executableRef, ModifierKind.ABSTRACT);
                boolean calleeIsPublic = calleeHasModifier(executableRef, ModifierKind.PUBLIC);
                boolean calleeIsPrivate = calleeHasModifier(executableRef, ModifierKind.PRIVATE);

                String previousStatementKind = previousStatementKind(invocation);
                String nextStatementKind = nextStatementKind(invocation);
                boolean previousStatementContainsMutation = previousStatementContainsMutation(invocation);
                boolean nextStatementUsesInvocationResult = nextStatementUsesInvocationResult(invocation);
                boolean invocationResultUsedInComparison = invocationResultUsedInComparison(invocation);
                boolean invocationResultUsedInNullCheck = invocationResultUsedInNullCheck(invocation);
                boolean invocationFeedsAnotherCall = invocationFeedsAnotherCall(invocation);

                boolean anyArgumentFromField = anyArgumentFromOrigin(invocation, "FIELD");
                boolean anyArgumentFromParameter = anyArgumentFromOrigin(invocation, "PARAMETER");
                boolean anyArgumentFromLocal = anyArgumentFromOrigin(invocation, "LOCAL");
                boolean anyArgumentFromInvocation = anyArgumentFromOrigin(invocation, "INVOCATION");
                boolean anyArgumentFromConstructor = anyArgumentFromOrigin(invocation, "CONSTRUCTOR");

                boolean isFactoryLikeCall = looksLikeFactoryMethod(methodName, invocation.getType());
                boolean returnsNewProjectType = returnsNewProjectType(invocation);
                boolean receiverLooksLikeFactory = receiverLooksLike(invocation, "factory", "builder", "creator", "supplier");

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
                        String.valueOf(isCollectionOperation),

                        String.valueOf(callerMethodFanOut),
                        String.valueOf(callerClassFanOut),
                        String.valueOf(calleeMethodFanIn),
                        String.valueOf(calleeClassFanIn),
                        formatDouble(callerMethodOutDegreeCentrality),
                        formatDouble(callerClassOutDegreeCentrality),
                        formatDouble(calleeMethodInDegreeCentrality),
                        formatDouble(calleeClassInDegreeCentrality),

                        String.valueOf(guard.guardedByIf),
                        String.valueOf(guard.guardedByNullCheck),
                        String.valueOf(guard.guardedByBooleanCheck),
                        String.valueOf(guard.guardedByInstanceofCheck),
                        String.valueOf(guard.precededByGuardClause),
                        String.valueOf(guard.branchReturnsOnGuard),
                        String.valueOf(guard.branchThrowsOnGuard),
                        String.valueOf(guard.branchContinuesToInvocation),
                        String.valueOf(guard.sameReceiverReferencedInGuard),
                        String.valueOf(guard.sameArgumentReferencedInGuard),

                        String.valueOf(receiverFlags.receiverIsProjectType),
                        String.valueOf(receiverFlags.receiverIsExternalType),
                        String.valueOf(receiverFlags.receiverIsFieldDependency),
                        String.valueOf(receiverFlags.receiverIsDomainType),
                        String.valueOf(receiverFlags.receiverIsCollectionType),
                        String.valueOf(receiverFlags.receiverIsOptionalType),
                        String.valueOf(receiverFlags.receiverIsStreamType),

                        String.valueOf(argumentFlags.anyArgumentIsProjectType),
                        String.valueOf(argumentFlags.anyArgumentIsExternalType),
                        String.valueOf(argumentFlags.anyArgumentIsDomainType),
                        String.valueOf(argumentFlags.anyArgumentIsCollectionType),
                        String.valueOf(argumentFlags.anyArgumentIsOptionalType),
                        String.valueOf(argumentFlags.anyArgumentIsPrimitiveLike),
                        String.valueOf(argumentFlags.anyArgumentIsStringLike),
                        String.valueOf(argumentFlags.anyArgumentIsBooleanLike),

                        String.valueOf(argumentFlags.hasStringLiteralArg),
                        String.valueOf(argumentFlags.hasNumericLiteralArg),
                        String.valueOf(argumentFlags.hasCharLiteralArg),
                        String.valueOf(argumentFlags.hasEnumArg),
                        String.valueOf(argumentFlags.literalArgumentCount),

                        String.valueOf(calleeDeclarationResolvable),
                        String.valueOf(calleeTypeResolvable),
                        String.valueOf(receiverTypeResolvable),
                        String.valueOf(allArgumentTypesResolvable),
                        String.valueOf(anyArgumentTypeUnknown),
                        String.valueOf(hasKnownReturnType),

                        String.valueOf(nameStartsWithNotify),
                        String.valueOf(nameStartsWithPublish),
                        String.valueOf(nameStartsWithEmit),
                        String.valueOf(nameStartsWithDispatch),
                        String.valueOf(nameStartsWithFire),
                        String.valueOf(nameStartsWithSend),
                        String.valueOf(receiverLooksLikeObserverPublisher),
                        String.valueOf(receiverLooksLikeEventBus),
                        String.valueOf(receiverLooksLikeListenerRegistry),
                        String.valueOf(anyArgumentLooksLikeEvent),
                        String.valueOf(anyArgumentLooksLikeMessage),
                        String.valueOf(anyArgumentLooksLikeListener),
                        String.valueOf(insideTransactionCallback),
                        String.valueOf(followsStateMutationNearby),

                        String.valueOf(callerContainsMultipleDistinctCallees),
                        String.valueOf(siblingInvocationCountInMethod),
                        String.valueOf(crossLayerCall),
                        String.valueOf(callsDependencyField),
                        String.valueOf(callsDifferentProjectComponentType),
                        String.valueOf(insideDelegationChain),
                        String.valueOf(hasChainedOrNestedDelegation),

                        String.valueOf(returnValueIgnored),
                        String.valueOf(returnsBoolean),
                        String.valueOf(returnsCollection),
                        String.valueOf(returnsOptional),
                        String.valueOf(returnsProjectType),
                        String.valueOf(returnsExternalType),
                        String.valueOf(methodLooksAccessor),
                        String.valueOf(methodLooksMutator),

                        String.valueOf(callerLooksQueryMethod),
                        String.valueOf(callerLooksCommandMethod),
                        String.valueOf(callerLooksControllerMethod),
                        String.valueOf(callerLooksFactoryMethod),
                        String.valueOf(callerLooksValidatorMethod),
                        String.valueOf(calleeLooksQueryMethod),
                        String.valueOf(calleeLooksCommandMethod),
                        String.valueOf(calleeLooksValidatorMethod),
                        String.valueOf(calleeLooksFactoryMethod),
                        String.valueOf(calleeLooksControllerMethod),

                        String.valueOf(callerIsPublic),
                        String.valueOf(callerIsPrivate),
                        String.valueOf(callerIsProtected),
                        String.valueOf(callerIsStatic),
                        String.valueOf(callerIsAbstract),
                        String.valueOf(calleeIsStatic),
                        String.valueOf(calleeIsAbstract),
                        String.valueOf(calleeIsPublic),
                        String.valueOf(calleeIsPrivate),

                        csv(previousStatementKind),
                        csv(nextStatementKind),
                        String.valueOf(previousStatementContainsMutation),
                        String.valueOf(nextStatementUsesInvocationResult),
                        String.valueOf(invocationResultUsedInComparison),
                        String.valueOf(invocationResultUsedInNullCheck),
                        String.valueOf(invocationFeedsAnotherCall),

                        csv(argumentOrigins),
                        String.valueOf(anyArgumentFromField),
                        String.valueOf(anyArgumentFromParameter),
                        String.valueOf(anyArgumentFromLocal),
                        String.valueOf(anyArgumentFromInvocation),
                        String.valueOf(anyArgumentFromConstructor),

                        String.valueOf(isFactoryLikeCall),
                        String.valueOf(returnsNewProjectType),
                        String.valueOf(methodNameStartsWithCreate),
                        String.valueOf(methodNameStartsWithBuild),
                        String.valueOf(methodNameStartsWithOf),
                        String.valueOf(methodNameStartsWithFrom),
                        String.valueOf(receiverLooksLikeFactory)
                ));
                writer.write("\n");
            }

            System.out.println("Total exported call sites: " + count);

        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private static void writeHeader(FileWriter writer) throws IOException {
        List<String> headers = new ArrayList<>();

        // Caller: compact caller identity at class#method-name granularity.
        // Computed from the declaring type qualified name and caller simple method name.
        // Matters because it is a human-readable identifier for grouping rows quickly.
        headers.add("Caller");

        // CallerSignature: fully qualified caller method signature.
        // Computed from declaring class qualified name + Spoon method signature.
        // Matters because graph metrics should use stable method identities, not just simple names.
        headers.add("CallerSignature");

        // Callee: compact callee identity at class#method-name granularity.
        // Computed from executable declaring type + callee simple name when resolvable.
        // Matters because it is the human-readable target label used in downstream inspection.
        headers.add("Callee");

        // CalleeSignature: fully qualified callee signature.
        // Computed from executable reference signature when available, with fallback reconstruction.
        // Matters because fan-in and method-level graph metrics need a stable callee key.
        headers.add("CalleeSignature");

        // CalleeParameterTypes: static parameter types of the called executable.
        // Computed from executable reference parameter type list.
        // Matters because overloads and API-shape differences affect role interpretation.
        headers.add("CalleeParameterTypes");

        // ReturnType: static return type of the invocation expression.
        // Computed from invocation.getType() with void/unknown fallback.
        // Matters because query/command/guard inference depends heavily on return shape.
        headers.add("ReturnType");

        // IsVoidCall: whether the invocation statically returns void.
        // Computed by checking the invocation type qualified name.
        // Matters because void-returning calls are stronger command/delegation signals.
        headers.add("IsVoidCall");

        // CallerPackage: package of the caller class.
        // Computed from caller declaring type package.
        // Matters because architectural layer inference starts from package placement.
        headers.add("CallerPackage");

        // CallerLayer: normalized caller architectural layer.
        // Computed from annotations first, then package heuristics.
        // Matters because controller/service/repository/domain distinctions drive many rules.
        headers.add("CallerLayer");

        // CalleeLayer: normalized callee architectural layer.
        // Computed from callee type when internal, otherwise external/unknown.
        // Matters because cross-layer behavior is useful for orchestration and dependency analysis.
        headers.add("CalleeLayer");

        // LayerRelation: simple caller->callee layer pair.
        // Computed by concatenating CallerLayer and CalleeLayer.
        // Matters because rule engines prefer flat normalized relation values.
        headers.add("LayerRelation");

        // IsInternal: whether the callee belongs to the analyzed project namespace.
        // Computed by checking the callee qualified name prefix against PROJECT_ROOT.
        // Matters because internal calls are more semantically trustworthy than framework calls.
        headers.add("IsInternal");

        // ResolutionQuality: coarse resolution status for the callee executable/type.
        // Computed from presence of executable reference and declaring type plus internal/external status.
        // Matters because unknown resolution should not be mistaken for meaningful negatives.
        headers.add("ResolutionQuality");

        // ArgCount: number of actual arguments at the call site.
        // Computed from invocation.getArguments().size().
        // Matters because arity is cheap signal for accessor/mutator/dispatcher-like patterns.
        headers.add("ArgCount");

        // HasLiteralArg: whether any actual argument is a literal.
        // Computed by scanning argument expressions for CtLiteral.
        // Matters because literals often indicate keys, flags, magic values, or routing information.
        headers.add("HasLiteralArg");

        // HasNullArg: whether any argument is the null literal.
        // Computed by scanning CtLiteral values for null.
        // Matters because null arguments are often tied to optionality, placeholder APIs, or poor hygiene.
        headers.add("HasNullArg");

        // HasBooleanArg: whether any argument is a boolean literal.
        // Computed by scanning literal values for Boolean.
        // Matters because booleans often indicate toggles, mode switches, and branch-sensitive behavior.
        headers.add("HasBooleanArg");

        // HasNestedInvocationArg: whether any argument contains a nested call.
        // Computed by checking for direct or descendant CtInvocation inside argument expressions.
        // Matters because nested calls are good evidence of chaining, delegation, or computed inputs.
        headers.add("HasNestedInvocationArg");

        // ArgumentStaticTypes: flattened static types of all actual arguments.
        // Computed from each argument expression type, with NULL/UNKNOWN normalization.
        // Matters because raw argument type shape is often useful in later feature engineering.
        headers.add("ArgumentStaticTypes");

        // Line: source line of the invocation.
        // Computed from the Spoon source position.
        // Matters because row traceability back to source is mandatory for debugging noisy classifications.
        headers.add("Line");

        // StandaloneStatement: whether the invocation itself is the enclosing statement.
        // Computed by comparing the nearest CtStatement parent with the invocation.
        // Matters because ignored results are strong indicators of commands or side-effecting calls.
        headers.add("StandaloneStatement");

        // ReturnUsed: whether the result is used in a larger expression.
        // Computed as the negation of StandaloneStatement.
        // Matters because result consumption distinguishes query-like use from fire-and-forget behavior.
        headers.add("ReturnUsed");

        // AssignedToVariable: whether the invocation result flows into a variable or assignment RHS.
        // Computed by checking local-variable initializer and assignment RHS containment.
        // Matters because this captures common query/dataflow usage patterns.
        headers.add("AssignedToVariable");

        // ReturnedDirectly: whether the invocation result is returned from the caller.
        // Computed by checking containment inside the nearest CtReturn returned expression.
        // Matters because direct returns are strong delegation/query evidence.
        headers.add("ReturnedDirectly");

        // PassedAsArgument: whether this invocation result is used as an argument to another call/constructor.
        // Computed by examining parent invocation and parent constructor arguments.
        // Matters because it marks composition/chaining behavior.
        headers.add("PassedAsArgument");

        // InIfCondition: whether the invocation appears inside an if-condition.
        // Computed by checking containment within the enclosing CtIf condition expression.
        // Matters because condition-position calls are often guard or query-like.
        headers.add("InIfCondition");

        // InsideIfBody: whether the invocation occurs inside then/else body but not condition.
        // Computed by checking containment in then/else statements and excluding condition membership.
        // Matters because guarded execution is different from guard evaluation.
        headers.add("InsideIfBody");

        // InsideLoop: whether the invocation is nested under a loop.
        // Computed via parent lookup for CtLoop.
        // Matters because iterative calls often indicate traversal, filtering, or repeated side effects.
        headers.add("InsideLoop");

        // InLoopCondition: whether the invocation appears in a loop condition.
        // Computed by inspecting looping expression where Spoon version permits, with fallback heuristic.
        // Matters because condition checks inside loops are role-relevant control signals.
        headers.add("InLoopCondition");

        // InsideTry: whether the call is inside a try block.
        // Computed via parent lookup for CtTry.
        // Matters because exception-aware placement can distinguish fragile or boundary calls.
        headers.add("InsideTry");

        // InsideCatch: whether the call is inside a catch block.
        // Computed via parent lookup for CtCatch.
        // Matters because error-recovery calls have different semantics from business logic calls.
        headers.add("InsideCatch");

        // InsideFinally: whether the call is inside a finally block.
        // Computed by checking containment inside the CtTry finalizer block.
        // Matters because cleanup/finalization logic is semantically distinct.
        headers.add("InsideFinally");

        // ThrowsHandledLocally: whether the call is enclosed by a try with at least one catch.
        // Computed from surrounding CtTry catchers.
        // Matters because locally handled failure can indicate defensive orchestration.
        headers.add("ThrowsHandledLocally");

        // InTernaryCondition: whether the call appears in a ternary condition.
        // Computed by checking containment in CtConditional condition expression.
        // Matters because condition-position invocations are often query/guard oriented.
        headers.add("InTernaryCondition");

        // InsideLambda: whether the call sits inside a lambda body.
        // Computed via parent lookup for CtLambda.
        // Matters because callbacks/functional pipelines often change the role interpretation.
        headers.add("InsideLambda");

        // InsideAnonymousClass: whether the call sits inside an anonymous class.
        // Computed via parent lookup for CtNewClass.
        // Matters because framework callbacks and listener implementations often appear here.
        headers.add("InsideAnonymousClass");

        // ReceiverCategory: coarse receiver semantic bucket.
        // Computed from receiver type-name heuristics and expression kind.
        // Matters because collection/service/repository/logger receivers imply very different intent.
        headers.add("ReceiverCategory");

        // ReceiverExpressionKind: syntactic receiver expression form.
        // Computed from the target expression runtime Spoon class.
        // Matters because this/field/static/chained receivers help distinguish delegation from local logic.
        headers.add("ReceiverExpressionKind");

        // ReceiverType: static type of the receiver expression.
        // Computed from invocation target type with implicit-this fallback.
        // Matters because raw receiver type remains valuable for auditing and later feature derivation.
        headers.add("ReceiverType");

        // ReceiverOrigin: where the receiver value comes from.
        // Computed from target expression analysis: this, field, local, parameter, chained call, constructor, etc.
        // Matters because dependency-field calls are stronger delegation signals than local temporaries.
        headers.add("ReceiverOrigin");

        // InvocationMode: broad dispatch mode.
        // Computed from target expression shape: implicit this, static, chained, constructor chain, instance.
        // Matters because static vs chained vs instance usage shifts interpretation.
        headers.add("InvocationMode");

        // MethodName: simple callee name.
        // Computed directly from executable reference.
        // Matters because name-prefix heuristics still pull a lot of weight in explainable rules.
        headers.add("MethodName");

        // NamePattern: coarse method-name stereotype.
        // Computed from prefixes and keywords such as get/save/validate/process.
        // Matters because this is a compact normalized naming signal for the rule engine.
        headers.add("NamePattern");

        headers.add("NameStartsWithGet");
        headers.add("NameStartsWithFind");
        headers.add("NameStartsWithSave");
        headers.add("NameStartsWithExists");
        headers.add("NameStartsWithDelete");
        headers.add("NameStartsWithUpdate");
        headers.add("NameStartsWithIs");
        headers.add("NameStartsWithHas");
        headers.add("NameContainsValidate");
        headers.add("NameContainsCheck");

        // BooleanLikeCall: whether name or return type suggests boolean semantics.
        // Computed from is/has/exists/can/should prefixes and boolean return type checks.
        // Matters because boolean-returning checks are strong guard/query evidence.
        headers.add("BooleanLikeCall");

        // CallerMethodNamePattern: coarse stereotype of the caller method name.
        // Computed from caller method simple name.
        // Matters because caller intent provides useful context for interpreting each contained call.
        headers.add("CallerMethodNamePattern");

        // CallerReturnType: caller method return type.
        // Computed from caller method declaration.
        // Matters because controller/query/command methods often differ by return shape.
        headers.add("CallerReturnType");

        // CallerClassRole: coarse role of the caller class.
        // Computed from annotations first, then naming/package heuristics.
        // Matters because class role contextualizes call-site intent.
        headers.add("CallerClassRole");

        // CallerAnnotations: flattened method+class annotation names.
        // Computed by collecting simple names from both caller method and type.
        // Matters because Spring/JUnit annotations are extremely informative context.
        headers.add("CallerAnnotations");

        headers.add("CallerTransactional");
        headers.add("CallerTest");
        headers.add("CallerRequestHandler");
        headers.add("CallerOverride");

        // CalleeAritySignature: normalized arity bucket.
        // Computed from arg count into ZERO/ONE/TWO/THREE/MANY.
        // Matters because compact buckets are easier to use in rule systems than raw counts alone.
        headers.add("CalleeAritySignature");

        // ArgumentTypePattern: syntactic pattern of actual arguments.
        // Computed from argument node kinds such as literal/variable/invocation/constructor.
        // Matters because delegation and computation often differ more by expression shape than raw types.
        headers.add("ArgumentTypePattern");

        // DistanceInCallChain: length of chained receiver-invocation chain.
        // Computed by walking target invocations backward.
        // Matters because longer chains often indicate fluent access, plumbing, or delegation.
        headers.add("DistanceInCallChain");

        // InternalResolutionQuality: simplified internal/external resolution flag.
        // Computed from callee type availability plus internal status.
        // Matters because downstream rules should distinguish unresolved from external.
        headers.add("InternalResolutionQuality");

        // CalleeModifiers: flattened modifiers of the resolved callee declaration.
        // Computed from executable declaration modifiers where resolvable.
        // Matters because static/public/abstract status influences interpretation.
        headers.add("CalleeModifiers");

        // IsCollectionOperation: whether the call looks like a collection or stream operation.
        // Computed from method-name heuristics plus receiver type-name heuristics.
        // Matters because collection plumbing should not be confused with domain behavior.
        headers.add("IsCollectionOperation");

        // CallerMethodFanOut: number of distinct callee methods called by the caller method.
        // Computed from the prebuilt method-level call graph using CallerSignature as source node.
        // Matters because high fan-out is strong orchestration/delegation signal.
        headers.add("CallerMethodFanOut");

        // CallerClassFanOut: number of distinct callee classes reached by the caller class.
        // Computed from the prebuilt class-level call graph using caller class as source node.
        // Matters because class-level breadth is useful for architecture and component coupling analysis.
        headers.add("CallerClassFanOut");

        // CalleeMethodFanIn: number of distinct caller methods targeting the callee method.
        // Computed from the reverse method-level call graph.
        // Matters because high fan-in often indicates utility, service, or central coordination APIs.
        headers.add("CalleeMethodFanIn");

        // CalleeClassFanIn: number of distinct caller classes targeting the callee class.
        // Computed from the reverse class-level call graph.
        // Matters because popular component classes often occupy architectural hubs.
        headers.add("CalleeClassFanIn");

        // CallerMethodOutDegreeCentrality: normalized method fan-out.
        // Computed as method fan-out divided by total method nodes minus one.
        // Matters because normalized metrics compare methods across projects and sizes better than raw counts.
        headers.add("CallerMethodOutDegreeCentrality");

        // CallerClassOutDegreeCentrality: normalized class fan-out.
        // Computed as class fan-out divided by total class nodes minus one.
        // Matters because it captures architectural reach at class granularity.
        headers.add("CallerClassOutDegreeCentrality");

        // CalleeMethodInDegreeCentrality: normalized method fan-in.
        // Computed as method fan-in divided by total method nodes minus one.
        // Matters because central methods deserve different treatment from leaf methods.
        headers.add("CalleeMethodInDegreeCentrality");

        // CalleeClassInDegreeCentrality: normalized class fan-in.
        // Computed as class fan-in divided by total class nodes minus one.
        // Matters because class hubs are common orchestration or infrastructure anchors.
        headers.add("CalleeClassInDegreeCentrality");

        // GuardedByIf: whether the invocation occurs inside an if-body guarded by a condition.
        // Computed by finding an enclosing CtIf and excluding condition-position invocations.
        // Matters because guarded execution is key for validate/guard classification.
        headers.add("GuardedByIf");

        // GuardedByNullCheck: whether the enclosing guard condition contains a null comparison.
        // Computed by scanning guard binary operators for ==/!= null.
        // Matters because null-guarded calls are a distinct and high-value defensive pattern.
        headers.add("GuardedByNullCheck");

        // GuardedByBooleanCheck: whether the enclosing guard appears boolean-like without being null/instanceof.
        // Computed from guard condition type and simple condition-shape heuristics.
        // Matters because it captures defensive predicates beyond explicit null checks.
        headers.add("GuardedByBooleanCheck");

        // GuardedByInstanceofCheck: whether the enclosing guard contains an instanceof test.
        // Computed by scanning guard binary operators for INSTANCEOF.
        // Matters because type refinement before invocation is strong contract-like evidence.
        headers.add("GuardedByInstanceofCheck");

        // PrecededByGuardClause: whether the immediately previous statement is a terminal guard if-statement.
        // Computed by inspecting the previous block statement and checking for return/throw/continue in one branch.
        // Matters because classic early-exit guard clauses are stronger than merely being inside an if-body.
        headers.add("PrecededByGuardClause");

        // BranchReturnsOnGuard: whether the preceding guard clause returns on the guarded branch.
        // Computed by checking for CtReturn in the previous guard branches.
        // Matters because return-based guards are common validation and short-circuit patterns.
        headers.add("BranchReturnsOnGuard");

        // BranchThrowsOnGuard: whether the preceding guard clause throws on the guarded branch.
        // Computed by checking for CtThrow in the previous guard branches.
        // Matters because thrown-contract violations are strong validation signals.
        headers.add("BranchThrowsOnGuard");

        // BranchContinuesToInvocation: whether control can reach this invocation after the preceding guard exits early.
        // Computed heuristically when an immediately preceding if contains a terminal branch.
        // Matters because this distinguishes actual precondition filtering from unrelated branching.
        headers.add("BranchContinuesToInvocation");

        // SameReceiverReferencedInGuard: whether symbols from the call receiver also appear in the guard condition.
        // Computed by collecting referenced symbols from receiver and guard expression and checking overlap.
        // Matters because guards tied to the same object are stronger evidence than generic guards.
        headers.add("SameReceiverReferencedInGuard");

        // SameArgumentReferencedInGuard: whether symbols from any argument also appear in the guard condition.
        // Computed by collecting argument and guard referenced symbols and checking overlap.
        // Matters because argument-specific validation is especially valuable for guard classification.
        headers.add("SameArgumentReferencedInGuard");

        // ReceiverIsProjectType: whether the receiver type belongs to the analyzed project.
        // Computed from receiver type qualified name prefix.
        // Matters because internal receivers usually carry more domain meaning than framework receivers.
        headers.add("ReceiverIsProjectType");

        // ReceiverIsExternalType: whether the receiver type is not a project type.
        // Computed as the complement of ReceiverIsProjectType when a receiver exists.
        // Matters because external receivers often indicate plumbing or library usage.
        headers.add("ReceiverIsExternalType");

        // ReceiverIsFieldDependency: whether the receiver originates from a field access/dependency.
        // Computed from ReceiverOrigin.
        // Matters because dependency-field calls are important for orchestration and delegation.
        headers.add("ReceiverIsFieldDependency");

        // ReceiverIsDomainType: whether the receiver type looks like an internal domain/model type.
        // Computed from internal package-name heuristics.
        // Matters because domain receivers often indicate business behavior, not framework plumbing.
        headers.add("ReceiverIsDomainType");

        // ReceiverIsCollectionType: whether the receiver type looks like a collection-like type.
        // Computed from receiver type-name heuristics.
        // Matters because collection operations should often be down-weighted semantically.
        headers.add("ReceiverIsCollectionType");

        // ReceiverIsOptionalType: whether the receiver type looks optional-like.
        // Computed from receiver type name containing optional.
        // Matters because Optional plumbing should not be mistaken for domain logic.
        headers.add("ReceiverIsOptionalType");

        // ReceiverIsStreamType: whether the receiver type looks stream-like.
        // Computed from receiver type name containing stream.
        // Matters because stream pipeline calls are often infrastructure-level chaining.
        headers.add("ReceiverIsStreamType");

        headers.add("AnyArgumentIsProjectType");
        headers.add("AnyArgumentIsExternalType");
        headers.add("AnyArgumentIsDomainType");
        headers.add("AnyArgumentIsCollectionType");
        headers.add("AnyArgumentIsOptionalType");
        headers.add("AnyArgumentIsPrimitiveLike");
        headers.add("AnyArgumentIsStringLike");
        headers.add("AnyArgumentIsBooleanLike");
        headers.add("HasStringLiteralArg");
        headers.add("HasNumericLiteralArg");
        headers.add("HasCharLiteralArg");
        headers.add("HasEnumArg");
        headers.add("LiteralArgumentCount");
        headers.add("CalleeDeclarationResolvable");
        headers.add("CalleeTypeResolvable");
        headers.add("ReceiverTypeResolvable");
        headers.add("AllArgumentTypesResolvable");
        headers.add("AnyArgumentTypeUnknown");
        headers.add("HasKnownReturnType");
        headers.add("NameStartsWithNotify");
        headers.add("NameStartsWithPublish");
        headers.add("NameStartsWithEmit");
        headers.add("NameStartsWithDispatch");
        headers.add("NameStartsWithFire");
        headers.add("NameStartsWithSend");
        headers.add("ReceiverLooksLikeObserverPublisher");
        headers.add("ReceiverLooksLikeEventBus");
        headers.add("ReceiverLooksLikeListenerRegistry");
        headers.add("AnyArgumentLooksLikeEvent");
        headers.add("AnyArgumentLooksLikeMessage");
        headers.add("AnyArgumentLooksLikeListener");
        headers.add("InsideTransactionCallback");
        headers.add("FollowsStateMutationNearby");
        headers.add("CallerContainsMultipleDistinctCallees");
        headers.add("SiblingInvocationCountInMethod");
        headers.add("CrossLayerCall");
        headers.add("CallsDependencyField");
        headers.add("CallsDifferentProjectComponentType");
        headers.add("InsideDelegationChain");
        headers.add("HasChainedOrNestedDelegation");
        headers.add("ReturnValueIgnored");
        headers.add("ReturnsBoolean");
        headers.add("ReturnsCollection");
        headers.add("ReturnsOptional");
        headers.add("ReturnsProjectType");
        headers.add("ReturnsExternalType");
        headers.add("MethodLooksAccessor");
        headers.add("MethodLooksMutator");
        headers.add("CallerLooksQueryMethod");
        headers.add("CallerLooksCommandMethod");
        headers.add("CallerLooksControllerMethod");
        headers.add("CallerLooksFactoryMethod");
        headers.add("CallerLooksValidatorMethod");
        headers.add("CalleeLooksQueryMethod");
        headers.add("CalleeLooksCommandMethod");
        headers.add("CalleeLooksValidatorMethod");
        headers.add("CalleeLooksFactoryMethod");
        headers.add("CalleeLooksControllerMethod");
        headers.add("CallerIsPublic");
        headers.add("CallerIsPrivate");
        headers.add("CallerIsProtected");
        headers.add("CallerIsStatic");
        headers.add("CallerIsAbstract");
        headers.add("CalleeIsStatic");
        headers.add("CalleeIsAbstract");
        headers.add("CalleeIsPublic");
        headers.add("CalleeIsPrivate");
        headers.add("PreviousStatementKind");
        headers.add("NextStatementKind");
        headers.add("PreviousStatementContainsMutation");
        headers.add("NextStatementUsesInvocationResult");
        headers.add("InvocationResultUsedInComparison");
        headers.add("InvocationResultUsedInNullCheck");
        headers.add("InvocationFeedsAnotherCall");
        headers.add("ArgumentOrigins");
        headers.add("AnyArgumentFromField");
        headers.add("AnyArgumentFromParameter");
        headers.add("AnyArgumentFromLocal");
        headers.add("AnyArgumentFromInvocation");
        headers.add("AnyArgumentFromConstructor");
        headers.add("IsFactoryLikeCall");
        headers.add("ReturnsNewProjectType");
        headers.add("MethodNameStartsWithCreate");
        headers.add("MethodNameStartsWithBuild");
        headers.add("MethodNameStartsWithOf");
        headers.add("MethodNameStartsWithFrom");
        headers.add("ReceiverLooksLikeFactory");

        writer.write(String.join(",", headers));
        writer.write("\n");
    }

    private static final class GraphStats {
        final Map<String, Set<String>> methodOut = new HashMap<>();
        final Map<String, Set<String>> classOut = new HashMap<>();
        final Map<String, Set<String>> methodIn = new HashMap<>();
        final Map<String, Set<String>> classIn = new HashMap<>();
        final Set<String> allMethodNodes = new HashSet<>();
        final Set<String> allClassNodes = new HashSet<>();

        int methodFanOut(String callerMethod) {
            return methodOut.getOrDefault(callerMethod, Collections.emptySet()).size();
        }

        int classFanOut(String callerClass) {
            return classOut.getOrDefault(callerClass, Collections.emptySet()).size();
        }

        int methodFanIn(String calleeMethod) {
            return methodIn.getOrDefault(calleeMethod, Collections.emptySet()).size();
        }

        int classFanIn(String calleeClass) {
            return classIn.getOrDefault(calleeClass, Collections.emptySet()).size();
        }

        double methodOutDegreeCentrality(String callerMethod) {
            int denom = Math.max(1, allMethodNodes.size() - 1);
            return ((double) methodFanOut(callerMethod)) / denom;
        }

        double classOutDegreeCentrality(String callerClass) {
            int denom = Math.max(1, allClassNodes.size() - 1);
            return ((double) classFanOut(callerClass)) / denom;
        }

        double methodInDegreeCentrality(String calleeMethod) {
            int denom = Math.max(1, allMethodNodes.size() - 1);
            return ((double) methodFanIn(calleeMethod)) / denom;
        }

        double classInDegreeCentrality(String calleeClass) {
            int denom = Math.max(1, allClassNodes.size() - 1);
            return ((double) classFanIn(calleeClass)) / denom;
        }
    }

    private static final class MethodSummary {
        final Map<String, Integer> invocationCountByMethod = new HashMap<>();
        final Map<String, Set<String>> distinctCalleesByMethod = new HashMap<>();
    }

    private static final class GuardFeatures {
        boolean guardedByIf;
        boolean guardedByNullCheck;
        boolean guardedByBooleanCheck;
        boolean guardedByInstanceofCheck;
        boolean precededByGuardClause;
        boolean branchReturnsOnGuard;
        boolean branchThrowsOnGuard;
        boolean branchContinuesToInvocation;
        boolean sameReceiverReferencedInGuard;
        boolean sameArgumentReferencedInGuard;
    }

    private static final class ReceiverTypeFlags {
        boolean receiverIsProjectType;
        boolean receiverIsExternalType;
        boolean receiverIsFieldDependency;
        boolean receiverIsDomainType;
        boolean receiverIsCollectionType;
        boolean receiverIsOptionalType;
        boolean receiverIsStreamType;
    }

    private static final class ArgumentTypeFlags {
        boolean anyArgumentIsProjectType;
        boolean anyArgumentIsExternalType;
        boolean anyArgumentIsDomainType;
        boolean anyArgumentIsCollectionType;
        boolean anyArgumentIsOptionalType;
        boolean anyArgumentIsPrimitiveLike;
        boolean anyArgumentIsStringLike;
        boolean anyArgumentIsBooleanLike;
        boolean hasStringLiteralArg;
        boolean hasNumericLiteralArg;
        boolean hasCharLiteralArg;
        boolean hasEnumArg;
        int literalArgumentCount;
        boolean allArgumentTypesResolvable = true;
        boolean anyArgumentTypeUnknown;
    }

    private static final class GuardClauseInfo {
        boolean precededByGuardClause;
        boolean branchReturnsOnGuard;
        boolean branchThrowsOnGuard;
        boolean branchContinuesToInvocation;
    }

    private static GraphStats buildGraphStats(List<CtInvocation<?>> invocations) {
        GraphStats stats = new GraphStats();

        for (CtInvocation<?> invocation : invocations) {
            CtMethod<?> callerMethod = invocation.getParent(CtMethod.class);
            CtType<?> callerType = callerMethod.getDeclaringType();
            CtExecutableReference<?> executableRef = invocation.getExecutable();
            CtTypeReference<?> calleeTypeRef = executableRef != null ? executableRef.getDeclaringType() : null;

            String callerMethodKey = callerType.getQualifiedName() + "#" + callerMethod.getSignature();
            String callerClassKey = callerType.getQualifiedName();
            String calleeMethodKey = deriveCalleeSignature(executableRef);
            String calleeClassKey = calleeTypeRef != null ? safeQualifiedName(calleeTypeRef) : "UNKNOWN";

            stats.allMethodNodes.add(callerMethodKey);
            stats.allMethodNodes.add(calleeMethodKey);
            stats.allClassNodes.add(callerClassKey);
            stats.allClassNodes.add(calleeClassKey);

            stats.methodOut.computeIfAbsent(callerMethodKey, k -> new LinkedHashSet<>()).add(calleeMethodKey);
            stats.classOut.computeIfAbsent(callerClassKey, k -> new LinkedHashSet<>()).add(calleeClassKey);
            stats.methodIn.computeIfAbsent(calleeMethodKey, k -> new LinkedHashSet<>()).add(callerMethodKey);
            stats.classIn.computeIfAbsent(calleeClassKey, k -> new LinkedHashSet<>()).add(callerClassKey);
        }

        return stats;
    }

    private static MethodSummary buildMethodSummary(List<CtInvocation<?>> invocations) {
        MethodSummary summary = new MethodSummary();

        for (CtInvocation<?> invocation : invocations) {
            CtMethod<?> callerMethod = invocation.getParent(CtMethod.class);
            CtType<?> callerType = callerMethod.getDeclaringType();
            CtExecutableReference<?> executableRef = invocation.getExecutable();

            String callerMethodKey = callerType.getQualifiedName() + "#" + callerMethod.getSignature();
            String calleeMethodKey = deriveCalleeSignature(executableRef);

            summary.invocationCountByMethod.merge(callerMethodKey, 1, Integer::sum);
            summary.distinctCalleesByMethod
                    .computeIfAbsent(callerMethodKey, k -> new LinkedHashSet<>())
                    .add(calleeMethodKey);
        }

        return summary;
    }

    private static String deriveCalleeSignature(CtExecutableReference<?> executableRef) {
        if (executableRef == null) {
            return "UNKNOWN";
        }

        String methodSig;
        try {
            methodSig = executableRef.getSignature();
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
            CtVariableReference<?> ref = target instanceof CtVariableRead<?>
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

    private static String deriveResolutionQuality(CtExecutableReference<?> executableRef,
                                                  CtTypeReference<?> calleeType,
                                                  boolean isInternal) {
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
            if (arg instanceof CtInvocation<?> || !arg.getElements(new TypeFilter<>(CtInvocation.class)).isEmpty()) {
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
            CtExpression<?> expr = localVar.getDefaultExpression();
            return invocation == expr || invocation.hasParent(expr);
        }

        CtAssignment<?, ?> assignment = invocation.getParent(CtAssignment.class);
        if (assignment == null || assignment.getAssignment() == null) {
            return false;
        }

        CtExpression<?> rhs = assignment.getAssignment();
        return invocation == rhs || invocation.hasParent(rhs);
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
        if (typeName.contains("collection") || typeName.contains("list") || typeName.contains("set")
                || typeName.contains("map") || typeName.contains("queue")) {
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

        if (lowerMethodName.startsWith("get") || lowerMethodName.startsWith("find") || lowerMethodName.startsWith("fetch")
                || lowerMethodName.startsWith("load") || lowerMethodName.startsWith("read")) {
            return "query";
        }

        if (lowerMethodName.startsWith("save") || lowerMethodName.startsWith("delete") || lowerMethodName.startsWith("update")
                || lowerMethodName.startsWith("remove") || lowerMethodName.startsWith("set")
                || lowerMethodName.startsWith("create") || lowerMethodName.startsWith("add")) {
            return "command";
        }

        if (lowerMethodName.startsWith("is") || lowerMethodName.startsWith("has") || lowerMethodName.startsWith("exists")
                || lowerMethodName.contains("check") || lowerMethodName.contains("validate")) {
            return "guard";
        }

        if (lowerMethodName.startsWith("process") || lowerMethodName.startsWith("handle") || lowerMethodName.startsWith("execute")) {
            return "orchestration";
        }

        return "other";
    }

    private static boolean isBooleanLikeCall(String lowerMethodName, CtTypeReference<?> typeRef) {
        if (lowerMethodName.startsWith("is") || lowerMethodName.startsWith("has") || lowerMethodName.startsWith("exists")
                || lowerMethodName.startsWith("can") || lowerMethodName.startsWith("should")) {
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

        if (lower.startsWith("get") || lower.startsWith("find") || lower.startsWith("list") || lower.startsWith("load")
                || lower.startsWith("fetch")) {
            return "query";
        }

        if (lower.startsWith("save") || lower.startsWith("create") || lower.startsWith("update")
                || lower.startsWith("delete") || lower.startsWith("remove") || lower.startsWith("set")) {
            return "command";
        }

        if (lower.startsWith("validate") || lower.startsWith("check") || lower.startsWith("verify")
                || lower.startsWith("assert")) {
            return "guard";
        }

        if (lower.startsWith("process") || lower.startsWith("handle") || lower.startsWith("execute") || lower.startsWith("run")) {
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
                } else if (value instanceof Character) {
                    parts.add("CHAR_LITERAL");
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

        Set<String> modifiers = new TreeSet<>();

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

        boolean methodLooksCollectionLike = lowerName.equals("add")
                || lowerName.equals("remove")
                || lowerName.equals("contains")
                || lowerName.equals("put")
                || lowerName.equals("get")
                || lowerName.equals("size")
                || lowerName.equals("clear")
                || lowerName.equals("stream")
                || lowerName.equals("map")
                || lowerName.equals("filter")
                || lowerName.equals("foreach");

        CtExpression<?> target = invocation.getTarget();
        if (target == null || target.getType() == null) {
            return methodLooksCollectionLike;
        }

        String typeName = safeQualifiedName(target.getType()).toLowerCase(Locale.ROOT);

        boolean receiverLooksCollectionLike = typeName.contains("collection")
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

    private static GuardFeatures deriveGuardFeatures(CtInvocation<?> invocation) {
        GuardFeatures f = new GuardFeatures();

        CtIf enclosingIf = invocation.getParent(CtIf.class);
        if (enclosingIf != null && !isInIfCondition(invocation)) {
            f.guardedByIf = true;

            CtExpression<Boolean> condition = enclosingIf.getCondition();
            if (condition != null) {
                f.guardedByNullCheck = expressionContainsNullCheck(condition);
                f.guardedByInstanceofCheck = expressionContainsInstanceof(condition);
                f.guardedByBooleanCheck = !f.guardedByNullCheck
                        && !f.guardedByInstanceofCheck
                        && expressionLooksBooleanGuard(condition);

                Set<String> guardRefs = collectReferencedSymbols(condition);
                Set<String> receiverRefs = collectReceiverSymbols(invocation);
                Set<String> argRefs = collectArgumentSymbols(invocation);

                f.sameReceiverReferencedInGuard = !Collections.disjoint(guardRefs, receiverRefs);
                f.sameArgumentReferencedInGuard = !Collections.disjoint(guardRefs, argRefs);
            }
        }

        GuardClauseInfo guardClause = derivePrecedingGuardClause(invocation);
        f.precededByGuardClause = guardClause.precededByGuardClause;
        f.branchReturnsOnGuard = guardClause.branchReturnsOnGuard;
        f.branchThrowsOnGuard = guardClause.branchThrowsOnGuard;
        f.branchContinuesToInvocation = guardClause.branchContinuesToInvocation;

        return f;
    }

    private static GuardClauseInfo derivePrecedingGuardClause(CtInvocation<?> invocation) {
        GuardClauseInfo info = new GuardClauseInfo();

        CtStatement stmt = enclosingStatementInBlock(invocation);
        CtBlock<?> block = stmt != null ? stmt.getParent(CtBlock.class) : null;
        if (stmt == null || block == null) {
            return info;
        }

        List<CtStatement> statements = block.getStatements();
        int idx = statements.indexOf(stmt);
        if (idx <= 0) {
            return info;
        }

        CtStatement prev = statements.get(idx - 1);
        if (!(prev instanceof CtIf)) {
            return info;
        }

        CtIf prevIf = (CtIf) prev;
        boolean thenTerminal = branchReturnsOrThrowsOrContinues(prevIf.getThenStatement());
        boolean elseTerminal = branchReturnsOrThrowsOrContinues(prevIf.getElseStatement());

        if (!thenTerminal && !elseTerminal) {
            return info;
        }

        info.precededByGuardClause = true;
        info.branchReturnsOnGuard = statementReturns(prevIf.getThenStatement()) || statementReturns(prevIf.getElseStatement());
        info.branchThrowsOnGuard = statementThrows(prevIf.getThenStatement()) || statementThrows(prevIf.getElseStatement());
        info.branchContinuesToInvocation = true;

        return info;
    }

    private static boolean expressionContainsNullCheck(CtExpression<?> expr) {
        for (CtBinaryOperator<?> op : expr.getElements(new TypeFilter<>(CtBinaryOperator.class))) {
            if ((op.getKind() == BinaryOperatorKind.EQ || op.getKind() == BinaryOperatorKind.NE)
                    && (isNullLiteral(op.getLeftHandOperand()) || isNullLiteral(op.getRightHandOperand()))) {
                return true;
            }
        }
        return false;
    }

    private static boolean expressionContainsInstanceof(CtExpression<?> expr) {
        for (CtBinaryOperator<?> op : expr.getElements(new TypeFilter<>(CtBinaryOperator.class))) {
            if (op.getKind() == BinaryOperatorKind.INSTANCEOF) {
                return true;
            }
        }
        return false;
    }

    private static boolean expressionLooksBooleanGuard(CtExpression<?> expr) {
        CtTypeReference<?> t = expr.getType();
        if (t != null) {
            String qn = safeQualifiedName(t);
            if ("boolean".equals(qn) || "java.lang.Boolean".equals(qn)) {
                return true;
            }
        }
        return expr instanceof CtUnaryOperator<?>
                || !expr.getElements(new TypeFilter<>(CtVariableRead.class)).isEmpty()
                || !expr.getElements(new TypeFilter<>(CtInvocation.class)).isEmpty();
    }

    private static boolean isNullLiteral(CtExpression<?> expr) {
        return expr instanceof CtLiteral<?> && ((CtLiteral<?>) expr).getValue() == null;
    }

    private static Set<String> collectReferencedSymbols(CtElement element) {
        Set<String> refs = new LinkedHashSet<>();
        if (element == null) {
            return refs;
        }

        for (CtVariableRead<?> read : element.getElements(new TypeFilter<>(CtVariableRead.class))) {
            if (read.getVariable() != null) {
                refs.add(read.getVariable().toString());
            }
        }
        for (CtVariableWrite<?> write : element.getElements(new TypeFilter<>(CtVariableWrite.class))) {
            if (write.getVariable() != null) {
                refs.add(write.getVariable().toString());
            }
        }
        for (CtFieldAccess<?> fa : element.getElements(new TypeFilter<>(CtFieldAccess.class))) {
            if (fa.getVariable() != null) {
                refs.add(fa.getVariable().toString());
            }
        }

        return refs;
    }

    private static Set<String> collectReceiverSymbols(CtInvocation<?> invocation) {
        CtExpression<?> target = invocation.getTarget();
        return target == null ? Collections.emptySet() : collectReferencedSymbols(target);
    }

    private static Set<String> collectArgumentSymbols(CtInvocation<?> invocation) {
        Set<String> refs = new LinkedHashSet<>();
        for (CtExpression<?> arg : invocation.getArguments()) {
            refs.addAll(collectReferencedSymbols(arg));
        }
        return refs;
    }

    private static ReceiverTypeFlags deriveReceiverTypeFlags(CtInvocation<?> invocation) {
        ReceiverTypeFlags f = new ReceiverTypeFlags();

        CtExpression<?> target = invocation.getTarget();
        CtTypeReference<?> type = target != null ? target.getType() : null;
        String qn = safeQualifiedName(type).toLowerCase(Locale.ROOT);

        f.receiverIsProjectType = isProjectType(type);
        f.receiverIsExternalType = type != null && !f.receiverIsProjectType;
        f.receiverIsFieldDependency = "FIELD".equals(deriveReceiverOrigin(invocation));
        f.receiverIsDomainType = isDomainType(type);
        f.receiverIsCollectionType = isCollectionType(type);
        f.receiverIsOptionalType = qn.contains("optional");
        f.receiverIsStreamType = qn.contains("stream");

        return f;
    }

    private static ArgumentTypeFlags deriveArgumentTypeFlags(CtInvocation<?> invocation) {
        ArgumentTypeFlags f = new ArgumentTypeFlags();

        for (CtExpression<?> arg : invocation.getArguments()) {
            if (arg == null) {
                f.anyArgumentTypeUnknown = true;
                f.allArgumentTypesResolvable = false;
                continue;
            }

            CtTypeReference<?> type = arg.getType();
            String qn = safeQualifiedName(type);

            if ("UNKNOWN".equals(qn)) {
                f.anyArgumentTypeUnknown = true;
                f.allArgumentTypesResolvable = false;
            }

            if (isProjectType(type)) f.anyArgumentIsProjectType = true;
            if (type != null && !isProjectType(type)) f.anyArgumentIsExternalType = true;
            if (isDomainType(type)) f.anyArgumentIsDomainType = true;
            if (isCollectionType(type)) f.anyArgumentIsCollectionType = true;
            if (isOptionalType(type)) f.anyArgumentIsOptionalType = true;
            if (isPrimitiveLike(type)) f.anyArgumentIsPrimitiveLike = true;
            if (isStringLike(type)) f.anyArgumentIsStringLike = true;
            if (isBooleanLike(type)) f.anyArgumentIsBooleanLike = true;

            if (arg instanceof CtLiteral<?>) {
                f.literalArgumentCount++;
                Object value = ((CtLiteral<?>) arg).getValue();
                if (value instanceof String) f.hasStringLiteralArg = true;
                if (value instanceof Number) f.hasNumericLiteralArg = true;
                if (value instanceof Character) f.hasCharLiteralArg = true;
            }

            if (type != null && type.isEnum()) {
                f.hasEnumArg = true;
            }
        }

        return f;
    }

    private static boolean isProjectType(CtTypeReference<?> type) {
        return type != null && safeQualifiedName(type).startsWith(PROJECT_ROOT);
    }

    private static boolean isDomainType(CtTypeReference<?> type) {
        if (type == null) return false;
        String qn = safeQualifiedName(type).toLowerCase(Locale.ROOT);
        return qn.startsWith(PROJECT_ROOT.toLowerCase(Locale.ROOT))
                && (qn.contains(".model.") || qn.contains(".domain."));
    }

    private static boolean isCollectionType(CtTypeReference<?> type) {
        if (type == null) return false;
        String qn = safeQualifiedName(type).toLowerCase(Locale.ROOT);
        return qn.contains("collection") || qn.contains("list") || qn.contains("set")
                || qn.contains("map") || qn.contains("queue") || qn.contains("iterable");
    }

    private static boolean isOptionalType(CtTypeReference<?> type) {
        return type != null && safeQualifiedName(type).toLowerCase(Locale.ROOT).contains("optional");
    }

    private static boolean isPrimitiveLike(CtTypeReference<?> type) {
        if (type == null) return false;
        String qn = safeQualifiedName(type);
        return type.isPrimitive()
                || "java.lang.Integer".equals(qn)
                || "java.lang.Long".equals(qn)
                || "java.lang.Double".equals(qn)
                || "java.lang.Float".equals(qn)
                || "java.lang.Short".equals(qn)
                || "java.lang.Byte".equals(qn)
                || "java.lang.Character".equals(qn)
                || "java.lang.Boolean".equals(qn);
    }

    private static boolean isStringLike(CtTypeReference<?> type) {
        return type != null && "java.lang.String".equals(safeQualifiedName(type));
    }

    private static boolean isBooleanLike(CtTypeReference<?> type) {
        if (type == null) return false;
        String qn = safeQualifiedName(type);
        return "boolean".equals(qn) || "java.lang.Boolean".equals(qn);
    }

    private static boolean isCalleeDeclarationResolvable(CtExecutableReference<?> executableRef) {
        if (executableRef == null) return false;
        try {
            return executableRef.getDeclaration() != null;
        } catch (Exception e) {
            return false;
        }
    }

    private static boolean isResolvable(CtTypeReference<?> type) {
        return type != null && !"UNKNOWN".equals(safeQualifiedName(type));
    }

    private static boolean isReceiverTypeResolvable(CtInvocation<?> invocation) {
        CtExpression<?> target = invocation.getTarget();
        return target == null || isResolvable(target.getType());
    }

    private static boolean receiverLooksLike(CtInvocation<?> invocation, String... tokens) {
        CtExpression<?> target = invocation.getTarget();
        if (target == null) return false;

        String text = (safeQualifiedName(target.getType()) + " " + target.toString()).toLowerCase(Locale.ROOT);
        for (String token : tokens) {
            if (text.contains(token.toLowerCase(Locale.ROOT))) {
                return true;
            }
        }
        return false;
    }

    private static boolean anyArgumentTypeNameContains(CtInvocation<?> invocation, String... tokens) {
        for (CtExpression<?> arg : invocation.getArguments()) {
            String text = (safeQualifiedName(arg.getType()) + " " + arg.toString()).toLowerCase(Locale.ROOT);
            for (String token : tokens) {
                if (text.contains(token.toLowerCase(Locale.ROOT))) {
                    return true;
                }
            }
        }
        return false;
    }

    private static boolean isInsideTransactionCallback(CtInvocation<?> invocation) {
        CtElement current = invocation;
        while (current != null) {
            if (current instanceof CtLambda<?> || current instanceof CtNewClass<?>) {
                CtInvocation<?> parentInvocation = current.getParent(CtInvocation.class);
                if (parentInvocation != null) {
                    String n = parentInvocation.getExecutable() != null
                            ? parentInvocation.getExecutable().getSimpleName().toLowerCase(Locale.ROOT)
                            : "";
                    String t = safeQualifiedName(parentInvocation.getTarget() != null ? parentInvocation.getTarget().getType() : null)
                            .toLowerCase(Locale.ROOT);
                    if (n.contains("execute") || n.contains("transaction") || t.contains("transaction")) {
                        return true;
                    }
                }
            }
            current = current.getParent();
        }
        return false;
    }

    private static boolean followsStateMutationNearby(CtInvocation<?> invocation) {
        CtStatement stmt = enclosingStatementInBlock(invocation);
        CtBlock<?> block = stmt != null ? stmt.getParent(CtBlock.class) : null;
        if (stmt == null || block == null) return false;

        List<CtStatement> statements = block.getStatements();
        int idx = statements.indexOf(stmt);
        if (idx <= 0) return false;

        CtStatement prev = statements.get(idx - 1);
        return statementContainsMutation(prev);
    }

    private static CtStatement enclosingStatementInBlock(CtInvocation<?> invocation) {
        CtElement cur = invocation;
        while (cur != null && !(cur.getParent() instanceof CtBlock)) {
            cur = cur.getParent();
        }
        return cur instanceof CtStatement ? (CtStatement) cur : null;
    }

    private static boolean statementContainsMutation(CtStatement stmt) {
        if (stmt == null) return false;
        if (!stmt.getElements(new TypeFilter<>(CtAssignment.class)).isEmpty()) return true;
        if (!stmt.getElements(new TypeFilter<>(CtVariableWrite.class)).isEmpty()) return true;

        for (CtInvocation<?> inv : stmt.getElements(new TypeFilter<>(CtInvocation.class))) {
            String n = inv.getExecutable() != null ? inv.getExecutable().getSimpleName().toLowerCase(Locale.ROOT) : "";
            if (n.startsWith("set") || n.startsWith("save") || n.startsWith("update") || n.startsWith("delete")
                    || n.startsWith("remove") || n.startsWith("add") || n.startsWith("put") || n.startsWith("clear")) {
                return true;
            }
        }
        return false;
    }

    private static boolean returnsBoolean(CtInvocation<?> invocation) {
        return isBooleanLike(invocation.getType());
    }

    private static boolean returnsCollection(CtInvocation<?> invocation) {
        return isCollectionType(invocation.getType());
    }

    private static boolean returnsOptional(CtInvocation<?> invocation) {
        return isOptionalType(invocation.getType());
    }

    private static boolean returnsProjectType(CtInvocation<?> invocation) {
        return isProjectType(invocation.getType());
    }

    private static boolean returnsExternalType(CtInvocation<?> invocation) {
        CtTypeReference<?> t = invocation.getType();
        return t != null && !isProjectType(t);
    }

    private static boolean methodLooksAccessor(String methodName, CtTypeReference<?> returnType) {
        String n = methodName == null ? "" : methodName.toLowerCase(Locale.ROOT);
        return n.startsWith("get") || n.startsWith("find") || n.startsWith("load") || n.startsWith("fetch")
                || (!"void".equals(safeQualifiedName(returnType)) && n.startsWith("is"));
    }

    private static boolean methodLooksMutator(String methodName, CtTypeReference<?> returnType) {
        String n = methodName == null ? "" : methodName.toLowerCase(Locale.ROOT);
        return n.startsWith("set") || n.startsWith("save") || n.startsWith("update")
                || n.startsWith("delete") || n.startsWith("remove") || n.startsWith("add")
                || ("void".equals(safeQualifiedName(returnType)) && n.startsWith("create"));
    }

    private static boolean looksLikeQueryMethod(String name, CtTypeReference<?> returnType, CtMethod<?> method, CtType<?> type) {
        String n = name == null ? "" : name.toLowerCase(Locale.ROOT);
        return n.startsWith("get") || n.startsWith("find") || n.startsWith("load")
                || n.startsWith("fetch") || n.startsWith("list")
                || (!"void".equals(safeQualifiedName(returnType)) && !looksLikeCommandMethod(name, returnType, method, type));
    }

    private static boolean looksLikeCommandMethod(String name, CtTypeReference<?> returnType, CtMethod<?> method, CtType<?> type) {
        String n = name == null ? "" : name.toLowerCase(Locale.ROOT);
        return n.startsWith("save") || n.startsWith("create") || n.startsWith("update")
                || n.startsWith("delete") || n.startsWith("remove") || n.startsWith("set")
                || "void".equals(safeQualifiedName(returnType));
    }

    private static boolean looksLikeValidatorMethod(String name, CtTypeReference<?> returnType) {
        String n = name == null ? "" : name.toLowerCase(Locale.ROOT);
        return n.startsWith("validate") || n.startsWith("check") || n.startsWith("verify")
                || n.startsWith("assert") || (isBooleanLike(returnType) && (n.startsWith("is") || n.startsWith("has")));
    }

    private static boolean looksLikeFactoryMethod(String name, CtTypeReference<?> returnType) {
        String n = name == null ? "" : name.toLowerCase(Locale.ROOT);
        return n.startsWith("create") || n.startsWith("build") || n.startsWith("of") || n.startsWith("from");
    }

    private static boolean looksLikeControllerMethod(CtMethod<?> method, CtType<?> type) {
        return hasAnyAnnotation(
                method, type,
                "RequestMapping", "GetMapping", "PostMapping", "PutMapping", "DeleteMapping", "PatchMapping",
                "Controller", "RestController"
        ) || "controller".equals(deriveClassRole(type));
    }

    private static boolean hasModifier(CtModifiable modifiable, ModifierKind kind) {
        return modifiable != null && modifiable.getModifiers().contains(kind);
    }

    private static boolean calleeHasModifier(CtExecutableReference<?> executableRef, ModifierKind kind) {
        if (executableRef == null) return false;
        try {
            CtExecutable<?> decl = executableRef.getDeclaration();
            return decl instanceof CtModifiable && ((CtModifiable) decl).getModifiers().contains(kind);
        } catch (Exception e) {
            return false;
        }
    }

    private static String previousStatementKind(CtInvocation<?> invocation) {
        CtStatement prev = previousStatement(invocation);
        return statementKind(prev);
    }

    private static String nextStatementKind(CtInvocation<?> invocation) {
        CtStatement next = nextStatement(invocation);
        return statementKind(next);
    }

    private static boolean previousStatementContainsMutation(CtInvocation<?> invocation) {
        return statementContainsMutation(previousStatement(invocation));
    }

    private static boolean nextStatementUsesInvocationResult(CtInvocation<?> invocation) {
        CtStatement next = nextStatement(invocation);
        if (next == null) return false;

        CtLocalVariable<?> localVar = invocation.getParent(CtLocalVariable.class);
        if (localVar != null && localVar.getDefaultExpression() != null) {
            String name = localVar.getSimpleName();
            return next.toString().contains(name);
        }

        CtAssignment<?, ?> assignment = invocation.getParent(CtAssignment.class);
        if (assignment != null && assignment.getAssigned() != null) {
            return next.toString().contains(assignment.getAssigned().toString());
        }

        return false;
    }

    private static boolean invocationResultUsedInComparison(CtInvocation<?> invocation) {
        CtBinaryOperator<?> op = invocation.getParent(CtBinaryOperator.class);
        return op != null && (
                op.getKind() == BinaryOperatorKind.EQ
                        || op.getKind() == BinaryOperatorKind.NE
                        || op.getKind() == BinaryOperatorKind.GE
                        || op.getKind() == BinaryOperatorKind.GT
                        || op.getKind() == BinaryOperatorKind.LE
                        || op.getKind() == BinaryOperatorKind.LT
        );
    }

    private static boolean invocationResultUsedInNullCheck(CtInvocation<?> invocation) {
        CtBinaryOperator<?> op = invocation.getParent(CtBinaryOperator.class);
        if (op == null) return false;
        return (op.getKind() == BinaryOperatorKind.EQ || op.getKind() == BinaryOperatorKind.NE)
                && (isNullLiteral(op.getLeftHandOperand()) || isNullLiteral(op.getRightHandOperand()));
    }

    private static boolean invocationFeedsAnotherCall(CtInvocation<?> invocation) {
        return isPassedAsArgument(invocation)
                || isPassedToAnotherInvocation(invocation)
                || invocation.getParent(CtInvocation.class) != null && invocation.getParent(CtInvocation.class) != invocation;
    }

    private static boolean isPassedToAnotherInvocation(CtInvocation<?> invocation) {
        CtInvocation<?> parentInvocation = invocation.getParent(CtInvocation.class);
        if (parentInvocation == null || parentInvocation == invocation) {
            return false;
        }
        return parentInvocation.getArguments().stream().anyMatch(arg -> arg == invocation || invocation.hasParent(arg));
    }

    private static CtStatement previousStatement(CtInvocation<?> invocation) {
        CtStatement stmt = enclosingStatementInBlock(invocation);
        CtBlock<?> block = stmt != null ? stmt.getParent(CtBlock.class) : null;
        if (stmt == null || block == null) return null;

        List<CtStatement> statements = block.getStatements();
        int idx = statements.indexOf(stmt);
        return idx > 0 ? statements.get(idx - 1) : null;
    }

    private static CtStatement nextStatement(CtInvocation<?> invocation) {
        CtStatement stmt = enclosingStatementInBlock(invocation);
        CtBlock<?> block = stmt != null ? stmt.getParent(CtBlock.class) : null;
        if (stmt == null || block == null) return null;

        List<CtStatement> statements = block.getStatements();
        int idx = statements.indexOf(stmt);
        return (idx >= 0 && idx + 1 < statements.size()) ? statements.get(idx + 1) : null;
    }

    private static String statementKind(CtStatement stmt) {
        if (stmt == null) return "NONE";
        if (stmt instanceof CtIf) return "IF";
        if (stmt instanceof CtReturn) return "RETURN";
        if (stmt instanceof CtThrow) return "THROW";
        if (stmt instanceof CtLoop) return "LOOP";
        if (stmt instanceof CtTry) return "TRY";
        if (stmt instanceof CtLocalVariable<?>) return "LOCAL_VARIABLE";
        if (stmt instanceof CtAssignment<?, ?>) return "ASSIGNMENT";
        if (stmt instanceof CtInvocation<?>) return "INVOCATION";
        return stmt.getClass().getSimpleName();
    }

    private static String deriveArgumentOrigins(CtInvocation<?> invocation) {
        List<String> parts = new ArrayList<>();
        for (CtExpression<?> arg : invocation.getArguments()) {
            parts.add(argumentOrigin(arg));
        }
        return parts.isEmpty() ? "NONE" : String.join("|", parts);
    }

    private static String argumentOrigin(CtExpression<?> arg) {
        if (arg == null) return "UNKNOWN";
        if (arg instanceof CtInvocation<?>) return "INVOCATION";
        if (arg instanceof CtConstructorCall<?>) return "CONSTRUCTOR";
        if (arg instanceof CtFieldAccess<?>) return "FIELD";
        if (arg instanceof CtVariableRead<?> || arg instanceof CtVariableWrite<?>) {
            CtVariableReference<?> ref = arg instanceof CtVariableRead<?>
                    ? ((CtVariableRead<?>) arg).getVariable()
                    : ((CtVariableWrite<?>) arg).getVariable();
            if (ref instanceof CtFieldReference<?>) return "FIELD";
            if (ref instanceof CtParameterReference<?>) return "PARAMETER";
            if (ref instanceof CtLocalVariableReference<?>) return "LOCAL";
            return "VARIABLE";
        }
        return arg.getClass().getSimpleName();
    }

    private static boolean anyArgumentFromOrigin(CtInvocation<?> invocation, String origin) {
        for (CtExpression<?> arg : invocation.getArguments()) {
            if (origin.equals(argumentOrigin(arg))) {
                return true;
            }
        }
        return false;
    }

    private static boolean returnsNewProjectType(CtInvocation<?> invocation) {
        return looksLikeFactoryMethod(
                invocation.getExecutable() != null ? invocation.getExecutable().getSimpleName() : "",
                invocation.getType()) && isProjectType(invocation.getType());
    }

    private static boolean startsWithAny(String value, String... prefixes) {
        String v = value == null ? "" : value.toLowerCase(Locale.ROOT);
        for (String p : prefixes) {
            if (v.startsWith(p.toLowerCase(Locale.ROOT))) {
                return true;
            }
        }
        return false;
    }

    private static String normalizeRole(String role) {
        return role == null ? "unknown" : role.toLowerCase(Locale.ROOT);
    }

    private static boolean branchReturnsOrThrowsOrContinues(CtStatement stmt) {
        return statementReturns(stmt) || statementThrows(stmt) || statementContinues(stmt);
    }

    private static boolean statementReturns(CtStatement stmt) {
        return stmt != null && (!stmt.getElements(new TypeFilter<>(CtReturn.class)).isEmpty() || stmt instanceof CtReturn<?>);
    }

    private static boolean statementThrows(CtStatement stmt) {
        return stmt != null && (!stmt.getElements(new TypeFilter<>(CtThrow.class)).isEmpty() || stmt instanceof CtThrow);
    }

    private static boolean statementContinues(CtStatement stmt) {
        return stmt != null && (!stmt.getElements(new TypeFilter<>(CtContinue.class)).isEmpty() || stmt instanceof CtContinue);
    }

    private static String formatDouble(double value) {
        return String.format(Locale.ROOT, "%.8f", value);
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
