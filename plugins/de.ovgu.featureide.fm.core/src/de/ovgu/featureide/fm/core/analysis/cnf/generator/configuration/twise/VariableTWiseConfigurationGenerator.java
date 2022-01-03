/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2020  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 *
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.ClauseList;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.AConfigurationGenerator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.ITWiseConfigurationGenerator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.ICoverStrategy.CombinationStatus;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.iterator.ICombinationSupplier;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.iterator.VariableTSingleIterator;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver.SelectionStrategy;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.monitor.MonitorThread;

/**
 * Variation of the {@link TWiseConfigurationGenerator} by Sebastian Krieter. Allows the usage of a matrix to compute different t-values for different parts of
 * an feature model.
 *
 * @author Karl Stoermer
 */
public class VariableTWiseConfigurationGenerator extends AConfigurationGenerator implements ITWiseConfigurationGenerator {

	private final class SamplingMonitor implements Runnable {

		@Override
		public void run() {
			if (VERBOSE) {
				final long uncoveredCount = (numberOfCombinations - coveredCount) - invalidCount;
				final double phaseProgress = ((int) Math.floor((1 - (((double) count) / numberOfCombinations)) * 1000)) / 10.0;
				final double coverProgress = ((int) Math.floor(((((double) coveredCount) / numberOfCombinations)) * 1000)) / 10.0;
				final double uncoverProgress = ((int) Math.floor(((((double) uncoveredCount) / numberOfCombinations)) * 1000)) / 10.0;
				final double invalidProgress = ((int) Math.floor(((((double) invalidCount) / numberOfCombinations)) * 1000)) / 10.0;
				final StringBuilder sb = new StringBuilder();

				sb.append(phaseCount);
				sb.append(" - ");
				sb.append(phaseProgress);
				sb.append(" (");
				sb.append(count);

				sb.append(") -- Configurations: ");
				sb.append(util.getIncompleteSolutionList().size() + util.getCompleteSolutionList().size());
				sb.append(" (");
				sb.append(util.getIncompleteSolutionList().size());
				sb.append(" | ");
				sb.append(util.getCompleteSolutionList().size());

				sb.append(") -- Covered: ");
				sb.append(coverProgress);
				sb.append(" (");
				sb.append(coveredCount);
				sb.append(")");

				sb.append(" -- Uncovered: ");
				sb.append(uncoverProgress);
				sb.append(" (");
				sb.append(uncoveredCount);
				sb.append(")");

				sb.append(" -- Invalid: ");
				sb.append(invalidProgress);
				sb.append(" (");
				sb.append(invalidCount);
				sb.append(")");
				System.out.println(sb.toString());
			}
		}
	}

	/**
	 * Converts a set of single literals into a grouped expression list.
	 *
	 * @param literalSet the literal set
	 * @return a grouped expression list (can be used as an input for the configuration generator).
	 */
	public static List<List<ClauseList>> convertLiterals(LiteralSet literalSet) {
		return TWiseCombiner.convertGroupedLiterals(Arrays.asList(literalSet));
	}

	/**
	 * Converts a grouped set of single literals into a grouped expression list.
	 *
	 * @param groupedLiterals the grouped literal sets
	 * @return a grouped expression list (can be used as an input for the configuration generator).
	 */
	public static List<List<ClauseList>> convertGroupedLiterals(List<LiteralSet> groupedLiterals) {
		return TWiseCombiner.convertGroupedLiterals(groupedLiterals);
	}

	/**
	 * Converts an expression list into a grouped expression set with a single group.
	 *
	 * @param expressions the expression list
	 * @return a grouped expression list (can be used as an input for the configuration generator).
	 */
	public static List<List<ClauseList>> convertExpressions(List<ClauseList> expressions) {
		return TWiseCombiner.convertExpressions(expressions);
	}

	// TODO Variation Point: Iterations of removing low-contributing Configurations
	private int iterations = 3;

	protected TWiseConfigurationUtil util;
//	protected TWiseCombiner combiner;

	protected final List<List<ClauseList>> nodes;
	protected final Map<List<List<ClauseList>>, Integer> mappedNodes;
	protected PresenceConditionManager presenceConditionManager;
	protected Map<PresenceConditionManager, Integer> groupPresenceConditionManagers;
	protected final Map<List<PresenceCondition>, Integer> mappedPresenceCondition;
	protected final List<Map.Entry<List<PresenceCondition>, Integer>> listedMappedPresenceCondition;

	protected long numberOfCombinations, count, coveredCount, invalidCount;
	protected int phaseCount;

	private List<TWiseConfiguration> curResult = null;
	private ArrayList<TWiseConfiguration> bestResult = null;

	protected MonitorThread samplingMonitor;
	private static List<LiteralSet> preConfigs;
	private static boolean initialized = false;

	public VariableTWiseConfigurationGenerator(CNF cnf, List<List<ClauseList>> nodes, Map<List<List<ClauseList>>, Integer> mappedNodes,
			List<LiteralSet> preConfigs) {
		super(cnf, Integer.MAX_VALUE);
		this.mappedNodes = mappedNodes;
		mappedPresenceCondition = new HashMap<>();
		listedMappedPresenceCondition = new ArrayList<>();
		this.nodes = nodes;
		VariableTWiseConfigurationGenerator.preConfigs = preConfigs;
	}

	public void init() {
		final CNF cnf = solver.getSatInstance();
		if (cnf.getClauses().isEmpty()) {
			util = new TWiseConfigurationUtil(cnf, null);
		} else {
			util = new TWiseConfigurationUtil(cnf, solver);
		}

		util.setMaxSampleSize(maxSampleSize);
		util.setRandom(getRandom());

		util.computeRandomSample();
		if (!util.getCnf().getClauses().isEmpty()) {
			util.computeMIG();
		}

		if ((preConfigs != null) || (preConfigs.size() != 0)) {
			util.setInitialConfigurations(preConfigs);
		}

//		groupPresenceConditionManagers.put(new PresenceConditionManager(util, nodes), null);
		mappedNodes.entrySet().stream().forEach(entry -> {
			final PresenceConditionManager pcm = new PresenceConditionManager(util, entry.getKey());
			mappedPresenceCondition.put(pcm.getGroupedPresenceConditions().get(0), entry.getValue());
		});
		listedMappedPresenceCondition.addAll(mappedPresenceCondition.entrySet().stream().collect(Collectors.toList()));

		solver.useSolutionList(0);
		solver.setSelectionStrategy(SelectionStrategy.ORG);
		initialized = true;
	}

	@Override
	protected void generate(IMonitor<List<LiteralSet>> monitor) throws Exception {
		if (!initialized) {
			init();
		}

		phaseCount = 0;

		for (int i = 0; i < iterations; i++) {
			trimConfigurationsVT();
			buildCombinations();
		}

		bestResult.forEach(configuration -> addResult(configuration.getCompleteSolution()));
	}

	// ____________________________________________________________________
	// adjusted for variable t
	private void trimConfigurationsVT() {
		if (curResult != null) {

			final VariableTWiseConfigurationStatistic statistic = new VariableTWiseConfigurationStatistic();
			final List<double[]> normConfigValuesList = new ArrayList<>();

			for (final Map.Entry<List<PresenceCondition>, Integer> entry : listedMappedPresenceCondition) {
				final List<List<PresenceCondition>> gPC = new ArrayList<>();
				gPC.add(entry.getKey());
				statistic.setT(entry.getValue());

				statistic.calculate(util, curResult, gPC);
				final double[] normConfigValues = statistic.getConfigValues2();
				normConfigValuesList.add(normConfigValues);
			}

			final double[] normConfigValues = new double[normConfigValuesList.get(0).length];
			for (int i = 0; i < normConfigValues.length; i++) {
				double td = 0;
				for (final double[] arr : normConfigValuesList) {
					td += arr[i];
				}
				normConfigValues[i] = td;
			}

			double mean = 0;
			for (final double d : normConfigValues) {
				mean += d;
			}
			mean /= normConfigValues.length;

			final double reference = mean;

			int index = 0;
			index = removeSolutions(normConfigValues, reference, index, util.getIncompleteSolutionList());
			index = removeSolutions(normConfigValues, reference, index, util.getCompleteSolutionList());
		}
	}

	private int removeSolutions(double[] values, final double reference, int index, List<TWiseConfiguration> solutionList) {
		for (final Iterator<TWiseConfiguration> iterator = solutionList.iterator(); iterator.hasNext();) {
			final TWiseConfiguration config = iterator.next();
			boolean protectSolution = false;
			check: for (final TWiseConfiguration given : util.getGivenSolutionList()) {
				if (config.getCompleteSolution().containsAll(given.getCompleteSolution())) {
					protectSolution = true;
					break check;
				}
			}
			if ((values[index++] < reference) && !protectSolution) {
				iterator.remove();
			}
		}
		return index;
	}

	private void buildCombinations() {
		final List<? extends ICoverStrategy> phaseList = Arrays.asList(//
				new CoverAll(util) //
		);

		final ICombinationSupplier<ClauseList> it;
		if (mappedPresenceCondition.size() > 0) {
			it = new VariableTSingleIterator(util.getCnf().getVariables().size(), listedMappedPresenceCondition);
		} else {
			it = null;
		}

		numberOfCombinations = it.size();
		if (numberOfCombinations == 0) {
			final LiteralSet[] solverSolutions = util.getSolverSolutions();
			if ((solverSolutions.length > 0) && (solverSolutions[0] != null)) {
				util.newConfiguration(solverSolutions[0]);
			}
		} else {
			coveredCount = 0;
			invalidCount = 0;

			samplingMonitor = new MonitorThread(new SamplingMonitor(), 60_000);
			try {
				samplingMonitor.start();
				final List<ClauseList> combinationListUncovered = new ArrayList<>();
				count = coveredCount;
				phaseCount++;
				ICoverStrategy phase = phaseList.get(0);
				while (true) {
					final ClauseList combinedCondition = it.get();
					if (combinedCondition == null) {
						break;
					}
					if (combinedCondition.isEmpty()) {
						invalidCount++;
					} else {
						final CombinationStatus covered = phase.cover(combinedCondition);
						switch (covered) {
						case NOT_COVERED:
							combinationListUncovered.add(combinedCondition);
							break;
						case COVERED:
							coveredCount++;
							combinedCondition.clear();
							break;
						case INVALID:
							invalidCount++;
							combinedCondition.clear();
							break;
						default:
							combinedCondition.clear();
							break;
						}
					}
					count++;
				}

				int coveredIndex = -1;
				for (int j = 1; j < phaseList.size(); j++) {
					phaseCount++;
					phase = phaseList.get(j);
					count = coveredCount + invalidCount;
					for (int i = coveredIndex + 1; i < combinationListUncovered.size(); i++) {
						final ClauseList combination = combinationListUncovered.get(i);
						final CombinationStatus covered = phase.cover(combination);
						switch (covered) {
						case COVERED:
							Collections.swap(combinationListUncovered, i, ++coveredIndex);
							coveredCount++;
							break;
						case NOT_COVERED:
							break;
						case INVALID:
							Collections.swap(combinationListUncovered, i, ++coveredIndex);
							invalidCount++;
							break;
						default:
							break;
						}
						count++;
					}
				}
			} finally {
				samplingMonitor.finish();
			}
		}

		curResult = util.getResultList();
		if ((bestResult == null) || (bestResult.size() > curResult.size())) {
			bestResult = new ArrayList<>(curResult.size());
			curResult.stream().map(TWiseConfiguration::clone).forEach(bestResult::add);
		}
	}

	public TWiseConfigurationUtil getUtil() {
		return util;
	}

	public int getIterations() {
		return iterations;
	}

	public void setIterations(int iterations) {
		this.iterations = iterations;
	}

	public List<LiteralSet> getCompleteConfigurations() {
		final List<LiteralSet> res = new ArrayList<>();
		util.getCompleteSolutionList().stream().forEach(config -> {
			res.add(config.getCompleteSolution());
		});
		return res;
	}

	/**
	 * @param config
	 * @return
	 */
	public Set<String> getCoveredInteractions(LiteralSet config) {

		final Set<String> coveredInteractions = new HashSet<>();
//		final ICombinationSupplier<ClauseList> it;
//		final List<List<PresenceCondition>> groupedPresenceConditions = presenceConditionManager.getGroupedPresenceConditions();
//		if (groupedPresenceConditions.size() == 1) {
//			it = new VariableTSingleIterator(util.getCnf().getVariables().size(), mappedPresenceCondition);
//		} else {
//			it = null;
//		}
		final ICombinationSupplier<ClauseList> it;
		if (mappedPresenceCondition.size() > 0) {
			it = new VariableTSingleIterator(util.getCnf().getVariables().size(), listedMappedPresenceCondition);
		} else {
			it = null;
		}

		ClauseList combinedCondition = it.get();
		while (combinedCondition != null) {

			if (combinedCondition.size() > 0) {
				final LiteralSet set = combinedCondition.get(0);

				if (config.containsAll(set)) {
					set.setOrder(de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet.Order.NATURAL);
					coveredInteractions.add(set.toString());
				}
			}

			combinedCondition = it.get();
		}

		return coveredInteractions;
	}

}
