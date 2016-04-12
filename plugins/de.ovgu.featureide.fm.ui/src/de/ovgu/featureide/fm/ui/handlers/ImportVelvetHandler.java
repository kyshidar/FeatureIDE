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
package de.ovgu.featureide.fm.ui.handlers;

import static de.ovgu.featureide.fm.core.localization.StringTable.VELVET;

import org.eclipse.swt.widgets.FileDialog;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.IFeatureModelReader;
import de.ovgu.featureide.fm.core.io.ModelIOFactory;
import de.ovgu.featureide.fm.ui.handlers.base.AbstractImportHandler;

/**
 * Reads a velvet feature model.
 * 
 * @author Sebastian Krieter
 * @author Marcus Pinnecke
 */
public class ImportVelvetHandler extends AbstractImportHandler {
	@Override
	protected IFeatureModelReader setModelReader(IFeatureModel fm) {
		return ModelIOFactory.getModelReader(fm, ModelIOFactory.TYPE_VELVET_IMPORT);
	}

	@Override
	protected IFeatureModel createFeatureModel() {
		return ModelIOFactory.getNewFeatureModel(ModelIOFactory.TYPE_VELVET_IMPORT);
	}

	@Override
	protected void setFilter(FileDialog fileDialog) {
		fileDialog.setFilterExtensions(new String[] { "*.velvet" });
		fileDialog.setFilterNames(new String[] { VELVET });
	}
}
