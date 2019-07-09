/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.io.manager;

import java.nio.file.Path;
import java.util.Objects;

import javax.annotation.CheckForNull;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;

/**
 * Responsible to load and save all information for a feature model instance.
 *
 * @author Sebastian Krieter
 */
public class FeatureModelManager extends AFileManager<IFeatureModel> implements IFeatureModelManager {

	private FeatureModelFormula persistentFormula = null;
	private FeatureModelFormula variableFormula = null;

	@CheckForNull
	public static FeatureModelManager getInstance(Path path) {
		return getInstance(path, true);
	}

	@CheckForNull
	public static final FeatureModelManager getInstance(Path identifier, boolean createInstance) {
		return getInstance(identifier, createInstance, FeatureModelManager.class);
	}

	public static IFeatureModelManager getInstance(IFeatureModel featureModel) {
		final IFeatureModelManager featureModelManager = getInstance(featureModel.getSourceFile());
		return (featureModelManager == null) ? new VirtualFeatureModelManager(featureModel) : featureModelManager;
	}

	public static final IFeatureModel load(Path path) {
		return FeatureModelIO.getInstance().load(path);
	}

	public static FileHandler<IFeatureModel> getFileHandler(Path path) {
		return FeatureModelIO.getInstance().getFileHandler(path);
	}

	public static final boolean save(IFeatureModel featureModel, Path path, IPersistentFormat<IFeatureModel> format) {
		return FeatureModelIO.getInstance().save(featureModel, path, format);
	}

	protected Object undoContext = null;

	protected FeatureModelManager(Path identifier) {
		super(identifier, FMFormatManager.getInstance(), FMFactoryManager.getInstance());
		variableObject.setSourceFile(identifier);
	}

	@Override
	public IFeatureModelFormat getFormat() {
		return (IFeatureModelFormat) super.getFormat();
	}

	@Override
	protected IFeatureModel copyObject(IFeatureModel oldObject) {
		final IFeatureModel clone = oldObject.clone();
		clone.setEventManager(this);
		return clone;
	}

	@Override
	public FeatureModelFormula getPersistentFormula() {
		if (persistentFormula == null) {
			persistentFormula = new FeatureModelFormula(persistentObject);
		}
		return persistentFormula;
	}

	@Override
	public FeatureModelFormula getVariableFormula() {
		fileOperationLock.lock();
		try {
			if (variableFormula == null) {
				variableFormula = new FeatureModelFormula(getSnapshot());
			}
			return variableFormula;
		} finally {
			fileOperationLock.unlock();
		}
	}

	@Override
	protected void resetSnapshot() {
		super.resetSnapshot();
		if ((variableFormula != null) && (variableObject != null)) {
			final Node oldNode = variableFormula.getPropositionalNode();
			final Node newNode = new FeatureModelFormula(variableObject).getPropositionalNode();
			if (!Objects.equals(oldNode, newNode)) {
				variableFormula = null;
			}
		}
	}

	@Override
	protected void setPersistentObject(IFeatureModel persistentObject) {
		super.setPersistentObject(persistentObject);
		persistentFormula = null;
	}

	@Override
	protected void setVariableObject(IFeatureModel variableObject) {
		if (this.variableObject != null) {
			for (final IEventListener listener : this.variableObject.getListeners()) {
				variableObject.addListener(listener);
			}
		}
		fileOperationLock.lock();
		try {
			super.setVariableObject(variableObject);
		} finally {
			fileOperationLock.unlock();
		}
	}

	@Override
	protected IFeatureModel createObject() throws Exception {
		final IFeatureModel featureModel = super.createObject();
		featureModel.setSourceFile(getPath());
		featureModel.setEventManager(this);
		return featureModel;
	}

	@Override
	public Object getUndoContext() {
		return undoContext;
	}

	@Override
	public void setUndoContext(Object undoContext) {
		this.undoContext = undoContext;
	}

	public static FeatureModelAnalyzer getAnalyzer(IFeatureModel fm) {
		return new FeatureModelAnalyzer(new FeatureModelFormula(fm));
	}

}
