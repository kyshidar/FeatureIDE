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
package de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.iterator;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import de.ovgu.featureide.fm.core.analysis.cnf.ClauseList;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.PresenceCondition;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.TWiseCombiner;

/**
 * TODO description
 *
 * @author Karl Stoermer
 */
public class VariableTSingleIterator implements ICombinationSupplier<ClauseList> {

	private final List<Map.Entry<List<PresenceCondition>, Integer>> mappedPresenceConditions;
	private final List<VariableTSupplierWrapper> mappedSuppliers;
	private final long numberOfCombinations;

	private final TWiseCombiner combiner;
	private PresenceCondition[] nextCombination;
	private int i;

	public VariableTSingleIterator(int n, List<Map.Entry<List<PresenceCondition>, Integer>> listedMappedPresenceCondition) {
		mappedPresenceConditions = new ArrayList<>();
		mappedPresenceConditions.addAll(listedMappedPresenceCondition);
		Collections.sort(mappedPresenceConditions, (a, b) -> a.getValue() > b.getValue() ? -1 : a.getValue() == b.getValue() ? 0 : 1);

		mappedSuppliers = new ArrayList<>();
		i = 0;

		combiner = new TWiseCombiner(n);
		nextCombination = new PresenceCondition[2];

		ICombinationSupplier<int[]> supplier;
		int count = 0;

		for (final Map.Entry<List<PresenceCondition>, Integer> entry : mappedPresenceConditions) {
			supplier = new RandomPartitionSupplier(entry.getValue(), entry.getKey().size());
			final VariableTSupplierWrapper vtsw = new VariableTSupplierWrapper(entry.getKey(), supplier, entry.getValue());
			mappedSuppliers.add(vtsw);
			count += supplier.size();
		}

		numberOfCombinations = count;
	}

	@Override
	public ClauseList get() {
		if (i < mappedSuppliers.size()) {
			final VariableTSupplierWrapper wrapper = mappedSuppliers.get(i);
			nextCombination = new PresenceCondition[wrapper.getT()];
			final int[] js = wrapper.getSupplier().get();
			if (js != null) {
				for (int j = 0; j < js.length; j++) {
					nextCombination[j] = wrapper.getPresenceConditions().get(js[j]);
				}
				final ClauseList combinedCondition = new ClauseList();
				combiner.combineConditions(nextCombination, combinedCondition);
				return combinedCondition;
			} else {
				i++;
				return get();
			}
		}
		return null;
	}

	@Override
	public long size() {
		return numberOfCombinations;
	}

}
