/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.Collection;

import org.prop4j.Node;
import org.prop4j.SatSolver;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.PropertyConstants;
import de.ovgu.featureide.fm.core.functional.Functional;

/**
 * Represents a propositional constraint below the feature diagram.
 * 
 * @author Thomas Thuem
 * @author Florian Proksch
 * @author Stefan Krueger
 */
public class Constraint implements PropertyConstants, IGraphicItem {

	public Constraint(IFeatureModel featureModel, Node propNode) {
		throw new UnsupportedOperationException("No longer supported");
	}

	public IConstraint constraint;

	public Constraint(IConstraint c) {
		this.constraint = c;
	}

	public void setLocation(FMPoint newLocation) {
		FeatureUtils.setLocation(constraint, newLocation);
	}

	public FMPoint getLocation() {
		return FeatureUtils.getLocation(constraint);
	}

	public FeatureModel getFeatureModel() {
		return FeatureUtils.convert(FeatureUtils.getFeatureModel(constraint));
	}

	public Collection<Feature> getDeadFeatures(SatSolver solver, FeatureModel fm, Collection<Feature> fmDeadFeatures) {
		return Functional.toList(Functional.map(
				FeatureUtils.getDeadFeatures(constraint, solver, FeatureUtils.convert(fm),
						Functional.toList(Functional.map(fmDeadFeatures, FeatureUtils.FEATURE_TO_IFEATURE))), FeatureUtils.IFEATURE_TO_FEATURE));
	}

	public Collection<Feature> getDeadFeatures(FeatureModel fm, Collection<Feature> fmDeadFeatures) {
		return Functional.toList(Functional.map(
				FeatureUtils.getDeadFeatures(constraint, FeatureUtils.convert(fm),
						Functional.toList(Functional.map(fmDeadFeatures, FeatureUtils.FEATURE_TO_IFEATURE))), FeatureUtils.IFEATURE_TO_FEATURE));
	}

	public void setConstraintAttribute(ConstraintAttribute attri, boolean fire) {
		FeatureUtils.setConstraintAttribute(constraint, attri, fire);
	}

	public ConstraintAttribute getConstraintAttribute() {
		return FeatureUtils.getConstraintAttribute(constraint);
	}

	public void setFeatureSelected(boolean selected) {
		FeatureUtils.setFeatureSelected(constraint, selected);
	}

	public boolean isFeatureSelected() {
		return FeatureUtils.isFeatureSelected(constraint);
	}

	public Node getNode() {
		return FeatureUtils.getNode(constraint);
	}

	public void setContainedFeatures() {
		FeatureUtils.setContainedFeatures(constraint);
	}

	public Collection<Feature> getContainedFeatures() {
		return Functional.toList(Functional.map(FeatureUtils.getContainedFeatures(constraint), FeatureUtils.IFEATURE_TO_FEATURE));
	}

	public boolean setFalseOptionalFeatures(FeatureModel clone, Collection<Feature> fmFalseOptionals) {
		return FeatureUtils.setFalseOptionalFeatures(constraint, FeatureUtils.convert(clone),
				Functional.toList(Functional.map(fmFalseOptionals, FeatureUtils.FEATURE_TO_IFEATURE)));
	}

	public boolean setFalseOptionalFeatures() {
		return FeatureUtils.setFalseOptionalFeatures(constraint);
	}

	public Collection<Feature> getFalseOptional() {
		return Functional.toList(Functional.map(FeatureUtils.getFalseOptional(constraint), FeatureUtils.IFEATURE_TO_FEATURE));
	}

	public void addListener(PropertyChangeListener listener) {
		FeatureUtils.addListener(constraint, listener);
	}

	public void removeListener(PropertyChangeListener listener) {
		FeatureUtils.removeListener(constraint, listener);
	}

	public void fire(PropertyChangeEvent event) {
		FeatureUtils.fire(constraint, event);
	}
	
	@Override
	public int hashCode() {
		return FeatureUtils.hashCode(constraint);
	};
	
	@Override
	public boolean equals(Object obj) {
		return FeatureUtils.equals(constraint, obj);
	}

	@Override
	public String toString() {
		return FeatureUtils.toString(constraint);
	}

	public boolean hasHiddenFeatures() {
		return FeatureUtils.hasHiddenFeatures(constraint);
	}

	public void setDeadFeatures(Collection<Feature> deadFeatures) {
		FeatureUtils.setDeadFeatures(constraint, Functional.toList(Functional.map(deadFeatures, FeatureUtils.FEATURE_TO_IFEATURE)));
	}

	public Collection<Feature> getDeadFeatures() {
		return Functional.toList(Functional.map(FeatureUtils.getDeadFeatures(constraint), FeatureUtils.IFEATURE_TO_FEATURE));
	}

	@Override
	public GraphicItem getItemType() {
		return FeatureUtils.getItemType(constraint);
	}

}
