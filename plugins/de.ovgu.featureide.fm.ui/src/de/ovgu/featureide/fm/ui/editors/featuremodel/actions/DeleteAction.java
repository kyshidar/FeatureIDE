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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.actions.ActionFactory;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ModelEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.ElementDeleteOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;

/**
 * Deletes the selected features and moves their unselected children upwards. Also deletes the selected propositional constraint.
 *
 * @author Thomas Thuem
 * @author Christian Becker
 * @author Marcus Pinnecke (Feature Interface)
 */
public class DeleteAction extends AFeatureModelAction {

	public static final String ID = ActionFactory.DELETE.getId();

	private static ImageDescriptor deleteImage = PlatformUI.getWorkbench().getSharedImages().getImageDescriptor(ISharedImages.IMG_TOOL_DELETE);

	private final Object viewer;

	private final ISelectionChangedListener listener = new ISelectionChangedListener() {

		@Override
		public void selectionChanged(SelectionChangedEvent event) {
			final IStructuredSelection selection = (IStructuredSelection) event.getSelection();
			setEnabled(isValidSelection(selection));
		}
	};

	public DeleteAction(Object viewer, IFeatureModelManager featureModelManager) {
		super("Delete (Del)", ID, featureModelManager);
		this.viewer = viewer;
		setImageDescriptor(deleteImage);
		setEnabled(false);
		if (viewer instanceof GraphicalViewerImpl) {
			((GraphicalViewerImpl) viewer).addSelectionChangedListener(listener);
		} else {
			((TreeViewer) viewer).addSelectionChangedListener(listener);
		}
	}

	@Override
	public void run() {
		FeatureModelOperationWrapper.run(new ElementDeleteOperation(viewer, featureModelManager));
	}

	private boolean isValidSelection(IStructuredSelection selection) {
		// check empty selection (i.e. ModelEditPart is selected)
		if ((selection.size() == 1) && (selection.getFirstElement() instanceof ModelEditPart)) {
			return false;
		}

		final IFeatureModel featureModel = featureModelManager.getSnapshot();
		// check that a possibly new root can be determined unique
		final IFeature root = featureModel.getStructure().getRoot().getFeature();
		IFeature newRoot = root;
		final LinkedList<IFeature> features = new LinkedList<>(featureModel.getFeatures());
		final Iterator<?> iter = selection.iterator();
		while (iter.hasNext()) {
			final Object editPart = iter.next();
			if (!(editPart instanceof FeatureEditPart) && !(editPart instanceof IFeature)) {
				continue;
			}
			final IFeature feature = editPart instanceof FeatureEditPart ? ((FeatureEditPart) editPart).getModel().getObject() : (IFeature) editPart;
			if (feature == root) {
				if (root.getStructure().getChildrenCount() != 1) {
					return false;
				}
				newRoot = root.getStructure().getFirstChild().getFeature();
				if (!newRoot.getStructure().hasChildren()) {
					return false;
				}
			}
			features.remove(feature);
		}

		// check that the only child of a deleted root is not deleted too
		if ((root != newRoot) && !features.contains(newRoot)) {
			return false;
		}

		if ((this instanceof ActionAllowedInExternalSubmodel) || !hasExternalFeature(selection)) {
			return true;
		}

		return false;

	}

	@Override
	protected List<IFeature> getInvolvedFeatures() {
		return ElementDeleteOperation.getFeatureNames(viewer).stream().map(f -> featureModelManager.getObject().getFeature(f)).collect(Collectors.toList());
	}
}
