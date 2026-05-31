package analysis;

import java.io.FileWriter;
import java.io.IOException;
import java.lang.annotation.Annotation;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
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
import spoon.reflect.code.CtConditional;
import spoon.reflect.code.CtConstructorCall;
import spoon.reflect.code.CtContinue;
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
import spoon.reflect.code.CtThrow;
import spoon.reflect.code.CtTypeAccess;
import spoon.reflect.code.CtUnaryOperator;
import spoon.reflect.code.CtVariableRead;
import spoon.reflect.code.CtVariableWrite;
import spoon.reflect.cu.SourcePosition;
import spoon.reflect.declaration.CtAnnotation;
import spoon.reflect.declaration.CtElement;
import spoon.reflect.declaration.CtExecutable;
import spoon.reflect.declaration.CtField;
import spoon.reflect.declaration.CtMethod;
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

    //private static final String PROJECT_ROOT = "org.springframework.samples.petclinic";
    //private static final String INPUT_RESOURCE = "/Users/mmilushev/VisualStudioProjects/CallSiteExtractor/spring-petclinic-main";

    //private static final String PROJECT_ROOT = "nl.tudelft.jpacman";
    //private static final String INPUT_RESOURCE = "/Users/mmilushev/VisualStudioProjects/CallSiteExtractor/jpacman-master";

    //The path should point to the module/classpath root for the project the extractor is run on.
    private static String PROJECT_ROOT = "com.fsck.k9";
    private static String INPUT_RESOURCE = "/Users/mmilushev/VisualStudioProjects/CallSiteExtractor/thunderbird-android-main/app";


    public static void main(String[] args) {
        configureInput(args);

        try (FileWriter writer = new FileWriter("calls.csv");
            FileWriter contextWriter = new FileWriter("calls_context.csv")) {
            writeHeader(writer);
            writeContextHeader(contextWriter);

            Launcher launcher = new Launcher();
            launcher.getEnvironment().setNoClasspath(true);
            launcher.getEnvironment().setComplianceLevel(8);
            launcher.addInputResource(INPUT_RESOURCE);
            launcher.buildModel();

            CtModel model = launcher.getModel();

            List<CtInvocation<?>> invocations = model.getElements(new TypeFilter<>(CtInvocation.class))
                    .stream()
                    .map(inv -> (CtInvocation<?>) inv)
                    .filter(inv -> inv.getParent(CtMethod.class) != null)
                    .filter(inv -> {
                        CtMethod<?> m = inv.getParent(CtMethod.class);
                        return m.getDeclaringType() != null;
                    })
                    .collect(Collectors.toList());

            GraphStats graphStats = buildGraphStats(invocations);

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

                int argCount = invocation.getArguments().size();
                String argumentTypePattern = deriveArgumentTypePattern(invocation);
                boolean hasLiteralArg = hasLiteralArg(invocation);
                boolean hasNullArg = hasNullArg(invocation);
                boolean hasBooleanArg = hasBooleanArg(invocation);
                boolean hasNestedInvocationArg = hasNestedInvocationArg(invocation);
                boolean assignedToVariable = isAssignedToVariable(invocation);
                boolean returnedDirectly = isReturnedDirectly(invocation);
                boolean passedAsArgument = isPassedAsArgument(invocation);
                boolean inIfCondition = isInIfCondition(invocation);
                boolean insideIfBody = isInsideIfBody(invocation);
                boolean insideLoop = invocation.getParent(CtLoop.class) != null;
                int line = extractLine(invocation);
                String receiverCategory = deriveReceiverCategory(invocation);
                String receiverOrigin = deriveReceiverOrigin(invocation);
                String lowerMethodName = methodName.toLowerCase(Locale.ROOT);
                boolean nameStartsWithGet = lowerMethodName.startsWith("get");
                boolean nameStartsWithFind = lowerMethodName.startsWith("find");
                boolean nameStartsWithSave = lowerMethodName.startsWith("save");
                boolean nameStartsWithDelete = lowerMethodName.startsWith("delete");
                boolean nameStartsWithUpdate = lowerMethodName.startsWith("update");
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
                int callerMethodFanOut = graphStats.methodFanOut(callerSignature);
                int callerClassFanOut = graphStats.classFanOut(callerClassName);
                int calleeMethodFanIn = graphStats.methodFanIn(calleeSignature);
                GuardFeatures guard = deriveGuardFeatures(invocation);
                ReceiverTypeFlags receiverFlags = deriveReceiverTypeFlags(invocation);
                boolean receiverLooksLikeObserverPublisher = receiverLooksLike(invocation, "publisher", "observer", "multicaster", "notifier");
                boolean receiverLooksLikeEventBus = receiverLooksLike(invocation, "eventbus", "eventpublisher", "applicationeventpublisher", "bus");
                boolean receiverLooksLikeListenerRegistry = receiverLooksLike(invocation, "listener", "registry", "subscriber");
                boolean anyArgumentLooksLikeEvent = anyArgumentTypeNameContains(invocation, "event");
                boolean anyArgumentLooksLikeMessage = anyArgumentTypeNameContains(invocation, "message", "payload", "notification");
                boolean followsStateMutationNearby = followsStateMutationNearby(invocation);
                boolean callsDependencyField = "FIELD".equals(deriveReceiverOrigin(invocation));
                boolean insideDelegationChain = isPassedAsArgument(invocation)
                        || isReturnedDirectly(invocation)
                        || isPassedToAnotherInvocation(invocation);
                boolean hasChainedOrNestedDelegation = "CHAINED".equals(deriveInvocationMode(invocation))
                        || hasNestedInvocationArg(invocation)
                        || isPassedToAnotherInvocation(invocation);
                boolean returnsBoolean = returnsBoolean(invocation);
                boolean returnsCollection = returnsCollection(invocation);
                boolean returnsOptional = returnsOptional(invocation);
                boolean returnsProjectType = returnsProjectType(invocation);
                boolean returnsExternalType = returnsExternalType(invocation);
                boolean methodLooksAccessor = methodLooksAccessor(methodName, invocation.getType());
                boolean methodLooksMutator = methodLooksMutator(methodName, invocation.getType());
                boolean callerLooksControllerMethod = looksLikeControllerMethod(callerMethod, callerType);
                boolean calleeLooksQueryMethod = looksLikeQueryMethod(methodName, invocation.getType(), null, null);
                boolean calleeLooksCommandMethod = looksLikeCommandMethod(methodName, invocation.getType(), null, null);
                boolean calleeLooksValidatorMethod = looksLikeValidatorMethod(methodName, invocation.getType());
                boolean previousStatementContainsMutation = previousStatementContainsMutation(invocation);
                boolean invocationResultUsedInComparison = invocationResultUsedInComparison(invocation);
                boolean invocationResultUsedInNullCheck = invocationResultUsedInNullCheck(invocation);
                boolean invocationFeedsAnotherCall = invocationFeedsAnotherCall(invocation);
                boolean isFactoryLikeCall = looksLikeFactoryMethod(methodName, invocation.getType());
                boolean returnsNewProjectType = returnsNewProjectType(invocation);
                boolean receiverLooksLikeFactory = receiverLooksLike(invocation, "factory", "builder", "creator", "supplier");
                String resultUsageKind = deriveResultUsageKind(invocation);
                String calleeNameAction = deriveCalleeNameAction(methodName);
                String computeTransformNameHint = deriveComputeTransformNameHint(methodName);
                String calleeBodySummary = deriveCalleeBodySummary(executableRef);
                String calleeAnnotations = extractCalleeAnnotations(executableRef);
                boolean receiverFieldInjectedDependency = isReceiverFieldInjectedDependency(invocation);
                boolean loggingCall = isLoggingCall(invocation, methodName);

                contextWriter.write(String.join(",",
                        csv(caller),
                        csv(callerSignature),
                        csv(callee),
                        csv(calleeSignature),
                        String.valueOf(line)
                ));
                contextWriter.write("\n");

                writer.write(String.join(",",
                        csv(returnType),
                        String.valueOf(isVoidCall),
                        csv(callerLayer),
                        csv(calleeLayer),
                        csv(layerRelation),
                        String.valueOf(argCount),
                        String.valueOf(hasLiteralArg),
                        String.valueOf(hasNullArg),
                        String.valueOf(hasBooleanArg),
                        String.valueOf(hasNestedInvocationArg),
                        String.valueOf(assignedToVariable),
                        String.valueOf(returnedDirectly),
                        String.valueOf(passedAsArgument),
                        String.valueOf(inIfCondition),
                        String.valueOf(insideIfBody),
                        String.valueOf(insideLoop),
                        csv(receiverCategory),
                        csv(receiverOrigin),
                        csv(methodName),
                        csv(namePattern),
                        String.valueOf(nameStartsWithGet),
                        String.valueOf(nameStartsWithFind),
                        String.valueOf(nameStartsWithSave),
                        String.valueOf(nameStartsWithDelete),
                        String.valueOf(nameStartsWithUpdate),
                        String.valueOf(nameContainsValidate),
                        String.valueOf(nameContainsCheck),
                        String.valueOf(booleanLikeCall),
                        csv(argumentTypePattern),
                        String.valueOf(callerMethodFanOut),
                        String.valueOf(callerClassFanOut),
                        String.valueOf(calleeMethodFanIn),
                        String.valueOf(guard.guardedByIf),
                        String.valueOf(guard.guardedByNullCheck),
                        String.valueOf(guard.guardedByBooleanCheck),
                        String.valueOf(guard.guardedByInstanceofCheck),
                        String.valueOf(guard.precededByGuardClause),
                        String.valueOf(receiverFlags.receiverIsProjectType),
                        String.valueOf(receiverFlags.receiverIsExternalType),
                        String.valueOf(receiverFlags.receiverIsFieldDependency),
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
                        String.valueOf(followsStateMutationNearby),
                        String.valueOf(crossLayerCall),
                        String.valueOf(callsDependencyField),
                        String.valueOf(insideDelegationChain),
                        String.valueOf(hasChainedOrNestedDelegation),
                        String.valueOf(returnsBoolean),
                        String.valueOf(returnsCollection),
                        String.valueOf(returnsOptional),
                        String.valueOf(returnsProjectType),
                        String.valueOf(returnsExternalType),
                        String.valueOf(methodLooksAccessor),
                        String.valueOf(methodLooksMutator),
                        String.valueOf(callerLooksControllerMethod),
                        String.valueOf(calleeLooksQueryMethod),
                        String.valueOf(calleeLooksCommandMethod),
                        String.valueOf(calleeLooksValidatorMethod),
                        String.valueOf(previousStatementContainsMutation),
                        String.valueOf(invocationResultUsedInComparison),
                        String.valueOf(invocationResultUsedInNullCheck),
                        String.valueOf(invocationFeedsAnotherCall),
                        String.valueOf(isFactoryLikeCall),
                        String.valueOf(returnsNewProjectType),
                        String.valueOf(methodNameStartsWithCreate),
                        String.valueOf(methodNameStartsWithBuild),
                        String.valueOf(methodNameStartsWithOf),
                        String.valueOf(methodNameStartsWithFrom),
                        String.valueOf(receiverLooksLikeFactory),
                        csv(resultUsageKind),
                        csv(calleeNameAction),
                        csv(computeTransformNameHint),
                        csv(calleeBodySummary),
                        csv(calleeAnnotations),
                        String.valueOf(receiverFieldInjectedDependency),
                        String.valueOf(loggingCall)
                ));
                writer.write("\n");
            }

            System.out.println("Total exported call sites: " + count);

        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private static void configureInput(String[] args) {
        PROJECT_ROOT = firstNonBlank(
                argValue(args, "--project-root"),
                System.getProperty("callExtractor.projectRoot"),
                System.getenv("CALL_EXTRACTOR_PROJECT_ROOT"),
                PROJECT_ROOT
        );
        INPUT_RESOURCE = firstNonBlank(
                argValue(args, "--input-resource"),
                System.getProperty("callExtractor.inputResource"),
                System.getenv("CALL_EXTRACTOR_INPUT_RESOURCE"),
                INPUT_RESOURCE
        );
    }

    private static String argValue(String[] args, String optionName) {
        if (args == null) {
            return null;
        }
        for (int i = 0; i < args.length; i++) {
            String arg = args[i];
            if (optionName.equals(arg) && i + 1 < args.length) {
                return args[i + 1];
            }
            String prefix = optionName + "=";
            if (arg != null && arg.startsWith(prefix)) {
                return arg.substring(prefix.length());
            }
        }
        return null;
    }

    private static String firstNonBlank(String... values) {
        for (String value : values) {
            if (value != null && !value.isBlank()) {
                return value;
            }
        }
        return "";
    }

    private static void writeContextHeader(FileWriter writer) throws IOException {
        writer.write("Caller,CallerSignature,Callee,CalleeSignature,Line\n");
    }

    private static void writeHeader(FileWriter writer) throws IOException {
        List<String> headers = new ArrayList<>();
        headers.add("ReturnType");
        headers.add("IsVoidCall");
        headers.add("CallerLayer");
        headers.add("CalleeLayer");
        headers.add("LayerRelation");
        headers.add("ArgCount");
        headers.add("HasLiteralArg");
        headers.add("HasNullArg");
        headers.add("HasBooleanArg");
        headers.add("HasNestedInvocationArg");
        headers.add("AssignedToVariable");
        headers.add("ReturnedDirectly");
        headers.add("PassedAsArgument");
        headers.add("InIfCondition");
        headers.add("InsideIfBody");
        headers.add("InsideLoop");
        headers.add("ReceiverCategory");
        headers.add("ReceiverOrigin");
        headers.add("MethodName");
        headers.add("NamePattern");
        headers.add("NameStartsWithGet");
        headers.add("NameStartsWithFind");
        headers.add("NameStartsWithSave");
        headers.add("NameStartsWithDelete");
        headers.add("NameStartsWithUpdate");
        headers.add("NameContainsValidate");
        headers.add("NameContainsCheck");
        headers.add("BooleanLikeCall");
        headers.add("ArgumentTypePattern");
        headers.add("CallerMethodFanOut");
        headers.add("CallerClassFanOut");
        headers.add("CalleeMethodFanIn");
        headers.add("GuardedByIf");
        headers.add("GuardedByNullCheck");
        headers.add("GuardedByBooleanCheck");
        headers.add("GuardedByInstanceofCheck");
        headers.add("PrecededByGuardClause");
        headers.add("ReceiverIsProjectType");
        headers.add("ReceiverIsExternalType");
        headers.add("ReceiverIsFieldDependency");
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
        headers.add("FollowsStateMutationNearby");
        headers.add("CrossLayerCall");
        headers.add("CallsDependencyField");
        headers.add("InsideDelegationChain");
        headers.add("HasChainedOrNestedDelegation");
        headers.add("ReturnsBoolean");
        headers.add("ReturnsCollection");
        headers.add("ReturnsOptional");
        headers.add("ReturnsProjectType");
        headers.add("ReturnsExternalType");
        headers.add("MethodLooksAccessor");
        headers.add("MethodLooksMutator");
        headers.add("CallerLooksControllerMethod");
        headers.add("CalleeLooksQueryMethod");
        headers.add("CalleeLooksCommandMethod");
        headers.add("CalleeLooksValidatorMethod");
        headers.add("PreviousStatementContainsMutation");
        headers.add("InvocationResultUsedInComparison");
        headers.add("InvocationResultUsedInNullCheck");
        headers.add("InvocationFeedsAnotherCall");
        headers.add("IsFactoryLikeCall");
        headers.add("ReturnsNewProjectType");
        headers.add("MethodNameStartsWithCreate");
        headers.add("MethodNameStartsWithBuild");
        headers.add("MethodNameStartsWithOf");
        headers.add("MethodNameStartsWithFrom");
        headers.add("ReceiverLooksLikeFactory");
        headers.add("ResultUsageKind");
        headers.add("CalleeNameAction");
        headers.add("ComputeTransformNameHint");
        headers.add("CalleeBodySummary");
        headers.add("CalleeAnnotations");
        headers.add("ReceiverFieldInjectedDependency");
        headers.add("IsLoggingCall");

        writer.write(String.join(",", headers));
        writer.write("\n");
    }

    private static final class GraphStats {
        final Map<String, Set<String>> methodOut = new HashMap<>();
        final Map<String, Set<String>> classOut = new HashMap<>();
        final Map<String, Set<String>> methodIn = new HashMap<>();

        int methodFanOut(String callerMethod) {
            return methodOut.getOrDefault(callerMethod, Collections.emptySet()).size();
        }

        int classFanOut(String callerClass) {
            return classOut.getOrDefault(callerClass, Collections.emptySet()).size();
        }

        int methodFanIn(String calleeMethod) {
            return methodIn.getOrDefault(calleeMethod, Collections.emptySet()).size();
        }
    }

    private static final class GuardFeatures {
        boolean guardedByIf;
        boolean guardedByNullCheck;
        boolean guardedByBooleanCheck;
        boolean guardedByInstanceofCheck;
        boolean precededByGuardClause;
    }

    private static final class ReceiverTypeFlags {
        boolean receiverIsProjectType;
        boolean receiverIsExternalType;
        boolean receiverIsFieldDependency;
    }

    private static final class GuardClauseInfo {
        boolean precededByGuardClause;
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

            stats.methodOut.computeIfAbsent(callerMethodKey, k -> new LinkedHashSet<>()).add(calleeMethodKey);
            stats.classOut.computeIfAbsent(callerClassKey, k -> new LinkedHashSet<>()).add(calleeClassKey);
            stats.methodIn.computeIfAbsent(calleeMethodKey, k -> new LinkedHashSet<>()).add(callerMethodKey);
        }

        return stats;
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

    private static Set<String> extractAnnotationSimpleNames(Collection<? extends CtAnnotation<? extends Annotation>> annotations) {
        Set<String> names = new TreeSet<>();
        for (CtAnnotation<?> annotation : annotations) {
            if (annotation.getAnnotationType() != null) {
                names.add(annotation.getAnnotationType().getSimpleName());
            }
        }
        return names;
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
            }
        }

        GuardClauseInfo guardClause = derivePrecedingGuardClause(invocation);
        f.precededByGuardClause = guardClause.precededByGuardClause;

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

    private static ReceiverTypeFlags deriveReceiverTypeFlags(CtInvocation<?> invocation) {
        ReceiverTypeFlags f = new ReceiverTypeFlags();

        CtExpression<?> target = invocation.getTarget();
        CtTypeReference<?> type = target != null ? target.getType() : null;

        f.receiverIsProjectType = isProjectType(type);
        f.receiverIsExternalType = type != null && !f.receiverIsProjectType;
        f.receiverIsFieldDependency = "FIELD".equals(deriveReceiverOrigin(invocation));

        return f;
    }

    private static boolean isProjectType(CtTypeReference<?> type) {
        return type != null && safeQualifiedName(type).startsWith(PROJECT_ROOT);
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

    private static boolean previousStatementContainsMutation(CtInvocation<?> invocation) {
        return statementContainsMutation(previousStatement(invocation));
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


    private static String deriveResultUsageKind(CtInvocation<?> invocation) {
        List<String> parts = new ArrayList<>();

        if (isAssignedToVariable(invocation)) {
            parts.add("ASSIGNED");
        }
        if (isReturnedDirectly(invocation)) {
            parts.add("RETURNED");
        }
        if (isPassedAsArgument(invocation)) {
            parts.add("PASSED_AS_ARGUMENT");
        }
        if (isInIfCondition(invocation) || isInLoopCondition(invocation) || isInTernaryCondition(invocation)) {
            parts.add("USED_IN_CONDITION");
        }
        if (invocationResultUsedInComparison(invocation)) {
            parts.add("USED_IN_COMPARISON");
        }
        if (invocationResultUsedInNullCheck(invocation)) {
            parts.add("USED_IN_NULL_CHECK");
        }
        if (isInvocationInChain(invocation)) {
            parts.add("CHAINED");
        }

        if (parts.isEmpty()) {
            parts.add(isEffectivelyIgnored(invocation) ? "IGNORED" : "OTHER_USED");
        }

        return String.join("|", parts);
    }

    private static boolean isInvocationInChain(CtInvocation<?> invocation) {
        if (invocation.getTarget() instanceof CtInvocation<?>) {
            return true;
        }

        CtInvocation<?> parentInvocation = invocation.getParent(CtInvocation.class);
        if (parentInvocation == null || parentInvocation == invocation) {
            return false;
        }

        CtExpression<?> parentTarget = parentInvocation.getTarget();
        return parentTarget != null && (parentTarget == invocation || invocation.hasParent(parentTarget));
    }

    private static boolean isEffectivelyIgnored(CtInvocation<?> invocation) {
        if (isVoidCall(invocation)) {
            return true;
        }

        if (invocation.getParent() instanceof CtBlock<?>) {
            return true;
        }

        CtStatement stmt = enclosingStatementInBlock(invocation);
        return stmt == invocation;
    }

    private static String deriveCalleeNameAction(String methodName) {
        String n = methodName == null ? "" : methodName.toLowerCase(Locale.ROOT);

        if (n.isBlank()) {
            return "OTHER";
        }
        if (isLoggingMethodName(n)) {
            return "LOGGER";
        }
        if (startsWithAny(n, "get", "read")) {
            return "ACCESSOR";
        }
        if (startsWithAny(n, "find", "fetch", "load", "list", "search", "query")) {
            return "FINDER";
        }
        if (startsWithAny(n, "exists", "is", "has", "can", "should")) {
            return "EXISTENCE_CHECK";
        }
        if (startsWithAny(n, "validate", "check", "verify", "assert") || n.contains("validate") || n.contains("check")) {
            return "VALIDATOR";
        }
        if (startsWithAny(n, "save", "persist", "store")) {
            return "PERSISTENCE";
        }
        if (startsWithAny(n, "delete", "remove")) {
            return "DELETION";
        }
        if (startsWithAny(n, "set", "update", "add", "put", "clear")) {
            return "MUTATOR";
        }
        if (startsWithAny(n, "notify", "publish", "emit", "fire", "send")) {
            return "NOTIFICATION";
        }
        if (startsWithAny(n, "dispatch", "handle", "process", "execute", "run")) {
            return "DISPATCHER";
        }
        if (startsWithAny(n, "convert", "transform", "map", "parse", "format", "normalize")) {
            return "CONVERSION";
        }
        if (startsWithAny(n, "compute", "calculate", "count", "sum", "average")) {
            return "CALCULATION";
        }
        if (startsWithAny(n, "create", "build", "of", "from", "new", "make")) {
            return "CREATION";
        }

        return "OTHER";
    }

    private static String deriveComputeTransformNameHint(String methodName) {
        String n = methodName == null ? "" : methodName.toLowerCase(Locale.ROOT);

        if (n.startsWith("compute")) return "COMPUTE";
        if (n.startsWith("calculate")) return "CALCULATE";
        if (n.startsWith("convert")) return "CONVERT";
        if (n.startsWith("map")) return "MAP";
        if (n.startsWith("transform")) return "TRANSFORM";
        if (n.startsWith("parse")) return "PARSE";
        if (n.startsWith("format")) return "FORMAT";
        if (n.startsWith("normalize")) return "NORMALIZE";
        if (n.startsWith("build")) return "BUILD";

        return "NONE";
    }

    private static String deriveCalleeBodySummary(CtExecutableReference<?> executableRef) {
        CtExecutable<?> decl = resolveExecutableDeclaration(executableRef);
        if (decl == null) {
            return "UNRESOLVED";
        }

        CtBlock<?> body;
        try {
            body = decl.getBody();
        } catch (Exception e) {
            return "UNRESOLVED";
        }

        if (body == null) {
            return "UNRESOLVED";
        }

        List<String> parts = new ArrayList<>();
        if (bodyWritesField(body)) {
            parts.add("WRITES_FIELD");
        }
        if (!body.getElements(new TypeFilter<>(CtAssignment.class)).isEmpty()
                || !body.getElements(new TypeFilter<>(CtVariableWrite.class)).isEmpty()) {
            parts.add("ASSIGNS_VARIABLE");
        }
        if (bodyCallsMutator(body)) {
            parts.add("CALLS_MUTATOR");
        }
        if (bodyReturnsValue(body)) {
            parts.add("RETURNS_VALUE");
        }
        if (bodyReturnsNewObject(body)) {
            parts.add("RETURNS_NEW_OBJECT");
        }
        if (!body.getElements(new TypeFilter<>(CtThrow.class)).isEmpty()) {
            parts.add("THROWS_EXCEPTION");
        }

        return parts.isEmpty() ? "NONE" : String.join("|", parts);
    }

    private static CtExecutable<?> resolveExecutableDeclaration(CtExecutableReference<?> executableRef) {
        if (executableRef == null) {
            return null;
        }

        try {
            return executableRef.getDeclaration();
        } catch (Exception e) {
            return null;
        }
    }

    private static boolean bodyWritesField(CtBlock<?> body) {
        for (CtAssignment<?, ?> assignment : body.getElements(new TypeFilter<>(CtAssignment.class))) {
            if (expressionTargetsField(assignment.getAssigned())) {
                return true;
            }
        }

        for (CtVariableWrite<?> write : body.getElements(new TypeFilter<>(CtVariableWrite.class))) {
            if (write.getVariable() instanceof CtFieldReference<?>) {
                return true;
            }
        }

        return false;
    }

    private static boolean expressionTargetsField(CtExpression<?> expression) {
        if (expression instanceof CtFieldAccess<?>) {
            return true;
        }
        if (expression instanceof CtVariableWrite<?>) {
            return ((CtVariableWrite<?>) expression).getVariable() instanceof CtFieldReference<?>;
        }
        return false;
    }

    private static boolean bodyCallsMutator(CtBlock<?> body) {
        for (CtInvocation<?> inv : body.getElements(new TypeFilter<>(CtInvocation.class))) {
            String name = inv.getExecutable() != null ? inv.getExecutable().getSimpleName() : "";
            if (methodLooksMutator(name, inv.getType())) {
                return true;
            }
        }
        return false;
    }

    private static boolean bodyReturnsValue(CtBlock<?> body) {
        for (CtReturn<?> ctReturn : body.getElements(new TypeFilter<>(CtReturn.class))) {
            if (ctReturn.getReturnedExpression() != null) {
                return true;
            }
        }
        return false;
    }

    private static boolean bodyReturnsNewObject(CtBlock<?> body) {
        for (CtReturn<?> ctReturn : body.getElements(new TypeFilter<>(CtReturn.class))) {
            CtExpression<?> returned = ctReturn.getReturnedExpression();
            if (returned instanceof CtConstructorCall<?>
                    || returned != null && !returned.getElements(new TypeFilter<>(CtConstructorCall.class)).isEmpty()) {
                return true;
            }
        }
        return false;
    }

    private static String extractCalleeAnnotations(CtExecutableReference<?> executableRef) {
        CtExecutable<?> decl = resolveExecutableDeclaration(executableRef);
        if (decl == null) {
            return "UNRESOLVED";
        }

        Set<String> names = new TreeSet<>();
        try {
            names.addAll(extractAnnotationSimpleNames(decl.getAnnotations()));
            CtType<?> declaringType = decl.getParent(CtType.class);
            if (declaringType != null) {
                names.addAll(extractAnnotationSimpleNames(declaringType.getAnnotations()));
            }
        } catch (Exception e) {
            return "UNRESOLVED";
        }

        return names.isEmpty() ? "NONE" : String.join("|", names);
    }

    private static boolean isReceiverFieldInjectedDependency(CtInvocation<?> invocation) {
        if (!"FIELD".equals(deriveReceiverOrigin(invocation))) {
            return false;
        }

        CtFieldReference<?> fieldRef = receiverFieldReference(invocation);
        if (fieldRef == null) {
            return false;
        }

        try {
            CtField<?> field = fieldRef.getDeclaration();
            if (field != null) {
                if (hasAnyAnnotationName(field.getAnnotations(), "Autowired", "Inject", "Resource")) {
                    return true;
                }
                if (looksLikeComponentType(field.getType())) {
                    return true;
                }
                if (field.getModifiers().contains(ModifierKind.FINAL)
                        && !isPrimitiveLike(field.getType())
                        && !isStringLike(field.getType())) {
                    return true;
                }
            }
        } catch (Exception ignored) {
        }

        return looksLikeComponentType(fieldRef.getType());
    }

    private static CtFieldReference<?> receiverFieldReference(CtInvocation<?> invocation) {
        CtExpression<?> target = invocation.getTarget();
        if (target instanceof CtFieldAccess<?>) {
            return ((CtFieldAccess<?>) target).getVariable();
        }

        if (target instanceof CtVariableRead<?> || target instanceof CtVariableWrite<?>) {
            CtVariableReference<?> ref = target instanceof CtVariableRead<?>
                    ? ((CtVariableRead<?>) target).getVariable()
                    : ((CtVariableWrite<?>) target).getVariable();
            if (ref instanceof CtFieldReference<?>) {
                return (CtFieldReference<?>) ref;
            }
        }

        return null;
    }

    private static boolean hasAnyAnnotationName(Collection<? extends CtAnnotation<? extends Annotation>> annotations,
                                                String... names) {
        Set<String> present = extractAnnotationSimpleNames(annotations);
        for (String name : names) {
            if (present.contains(name)) {
                return true;
            }
        }
        return false;
    }

    private static boolean looksLikeComponentType(CtTypeReference<?> type) {
        if (type == null) {
            return false;
        }

        String qn = safeQualifiedName(type).toLowerCase(Locale.ROOT);
        return qn.contains("service")
                || qn.contains("repository")
                || qn.contains("controller")
                || qn.contains("component")
                || qn.contains("client")
                || qn.contains("publisher")
                || qn.contains("notifier")
                || qn.contains("validator")
                || qn.contains("handler")
                || qn.contains("manager")
                || qn.contains("facade")
                || qn.contains("gateway")
                || qn.contains("factory")
                || qn.contains("dao");
    }

    private static boolean isLoggingCall(CtInvocation<?> invocation, String methodName) {
        String n = methodName == null ? "" : methodName.toLowerCase(Locale.ROOT);
        if (!isLoggingMethodName(n)) {
            return false;
        }

        CtExpression<?> target = invocation.getTarget();
        if (target == null) {
            return false;
        }

        String text = (safeQualifiedName(target.getType()) + " " + target).toLowerCase(Locale.ROOT);
        return text.contains("logger") || text.contains("slf4j") || text.contains("log4j") || text.contains("log");
    }

    private static boolean isLoggingMethodName(String lowerMethodName) {
        return "trace".equals(lowerMethodName)
                || "debug".equals(lowerMethodName)
                || "info".equals(lowerMethodName)
                || "warn".equals(lowerMethodName)
                || "error".equals(lowerMethodName)
                || "fatal".equals(lowerMethodName)
                || "log".equals(lowerMethodName);
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
