/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.analysis.cnf.manipulator.remove.heuristic;

import de.ovgu.featureide.fm.core.analysis.cnf.manipulator.remove.DeprecatedFeature;

/**
 * Implementation of {@link AFeatureOrderHeuristic}. Returns features dependent on the current clauses in the formula.
 *
 * @author Sebastian Krieter
 */
public class MinimumClauseHeuristic extends AFeatureOrderHeuristic {

	public MinimumClauseHeuristic(DeprecatedFeature[] map, int length) {
		super(map, length);
	}

	@Override
	protected int getNextIndex() {
		DeprecatedFeature smallestFeature = map[1];
		int minIndex = 1;
		for (int i = 2; i < map.length; i++) {
			final DeprecatedFeature next = map[i];
			if ((smallestFeature == null) || ((next != null) && ((smallestFeature.getClauseCount() - next.getClauseCount()) > 0))) {
				smallestFeature = next;
				minIndex = i;
			}
		}
		return minIndex;
	}

}
