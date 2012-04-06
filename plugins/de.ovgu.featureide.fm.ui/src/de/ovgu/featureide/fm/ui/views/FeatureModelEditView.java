/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.views;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.File;
import java.io.FileNotFoundException;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.draw2d.ConnectionLayer;
import org.eclipse.gef.LayerConstants;
import org.eclipse.gef.editparts.ScalableFreeformRootEditPart;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.gef.ui.parts.ScrollingGraphicalViewer;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.progress.UIJob;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.editing.evaluation.Evaluation;
import de.ovgu.featureide.fm.core.io.FeatureModelReaderIFileWrapper;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;
import de.ovgu.featureide.fm.core.propertypage.IPersistentPropertyManager;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GEFImageWriter;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.GraphicalEditPartFactory;
import de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.FeatureDiagramLayoutManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.LevelOrderLayout;
import de.ovgu.featureide.fm.ui.views.featuremodeleditview.ViewContentProvider;
import de.ovgu.featureide.fm.ui.views.featuremodeleditview.ViewLabelProvider;

/**
 * A view to calculate the category an edit. Given an open feature model editor
 * the current editing version is compared to the last saved model.
 * 
 * @author Thomas Thuem
 */
public class FeatureModelEditView extends ViewPart implements GUIDefaults {

	public static final String ID = FMUIPlugin.PLUGIN_ID
			+ ".views.FeatureModelEditView";

	public static final Image REFESH_TAB_IMAGE = FMUIPlugin.getImage("refresh_tab.gif");

	private static final QualifiedName ACTIVATOR_KEY = new QualifiedName(FMUIPlugin.PLUGIN_ID + ".EditViewActivator", FMUIPlugin.PLUGIN_ID + ".EditViewActivator");

	private static final String ACTIVATOR_ACTION_TEXT = "Disable automatic calculations";
	private static final String MANUAL_CALCULATION_TEXT = "Start calculation";
	
	private IWorkspaceRoot workspaceRoot;
	
	private TreeViewer viewer;

	private FeatureModelEditor featureModelEditor;

	private Job job;
	
	/**
	 * Button to start manual calculations.
	 */
	private Action manualAction = new Action() {
		public void run() {
			Job job = new Job("Updating Feature Model Edits") {
				protected IStatus run(IProgressMonitor monitor) {
					if (featureModelEditor == null)
						contentProvider.defaultContent();
					else {
						contentProvider.calculateContent(
								featureModelEditor.getOriginalFeatureModel(),
								featureModelEditor.getFeatureModel());
					}
					return Status.OK_STATUS;
				}
			};
			job.setPriority(Job.SHORT);
			job.schedule();
		}
	};
	
	/**
	 * Button to enable/disable automatic calculations.
	 */
	private Action activatorAction = new Action() {
		public void run() {
			Job job = new Job("") {
				protected IStatus run(IProgressMonitor monitor) {
					activatorAction.setChecked(activatorAction.isChecked());
					manualAction.setEnabled(activatorAction.isChecked());
					setActivatorChecked(activatorAction.isChecked());
					return Status.OK_STATUS;
				}

			};
			job.setPriority(Job.SHORT);
			job.schedule();
		}
	};
	
	private IPartListener editorListener = new IPartListener() {

		public void partOpened(IWorkbenchPart part) {
		}

		public void partDeactivated(IWorkbenchPart part) {
		}

		public void partClosed(IWorkbenchPart part) {
			if (part == featureModelEditor)
				setFeatureModelEditor(null);
		}

		public void partBroughtToTop(IWorkbenchPart part) {
			if (part instanceof IEditorPart)
				setFeatureModelEditor(part);
		}

		public void partActivated(IWorkbenchPart part) {
		}

	};

	private PropertyChangeListener modelListener = new PropertyChangeListener() {
		public void propertyChange(PropertyChangeEvent evt) {
			refresh();
		}
	};

	private ViewContentProvider contentProvider = new ViewContentProvider(this);

	public void createPartControl(Composite parent) {
		viewer = new TreeViewer(parent, SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL);
		viewer.setContentProvider(contentProvider);
		viewer.setLabelProvider(new ViewLabelProvider());
		viewer.setInput(getViewSite());

		getSite().getPage().addPartListener(editorListener);
		IWorkbenchPage page = getSite().getPage();
		setFeatureModelEditor(page.getActiveEditor());
		
		fillLocalToolBar(getViewSite().getActionBars().getToolBarManager());
	}

	/**
	 * @param toolBarManager
	 */
	private void fillLocalToolBar(IToolBarManager manager) {
		manager.add(activatorAction);
		if (workspaceRoot == null) {
			activatorAction.setEnabled(false);
		}
		activatorAction.setChecked(isActivatorChecked());
		activatorAction.setToolTipText(ACTIVATOR_ACTION_TEXT);
		activatorAction.setImageDescriptor(ImageDescriptor.createFromImage(REFESH_TAB_IMAGE));
		
		manager.add(manualAction);
		manualAction.setEnabled(activatorAction.isChecked());
		manualAction.setToolTipText(MANUAL_CALCULATION_TEXT);
		manualAction.setImageDescriptor(ImageDescriptor.createFromImage(REFESH_TAB_IMAGE));
	}

	/**
	 * @return The persistent property status of the activator action
	 */
	private boolean isActivatorChecked() {
		if (workspaceRoot != null) {
			try {
				return "true".equals(workspaceRoot.getPersistentProperty(ACTIVATOR_KEY));
			} catch (CoreException e) {
				FMUIPlugin.getDefault().logError(e);
			}
		}
		return false;
	}
	
	/**
	 * Sets the persistent property status of the activator action.
	 * @param checked The new status
	 */
	private void setActivatorChecked(boolean checked) {
		if (workspaceRoot != null) {
			try {
				workspaceRoot.setPersistentProperty(ACTIVATOR_KEY, checked ? "true" : "false");
			} catch (CoreException e) {
				FMUIPlugin.getDefault().logError(e);
			}
		}
	}

	@Override
	public void dispose() {
		if (job != null) {
			if (job.getState() == Job.RUNNING)
				job.cancel();
			job = null;
		}
		getSite().getPage().removePartListener(editorListener);
		if (featureModelEditor != null) {
			featureModelEditor.getOriginalFeatureModel().removeListener(
					modelListener);
			featureModelEditor.getFeatureModel().removeListener(modelListener);
			featureModelEditor = null;
		}
		super.dispose();
	}

	/**
	 * Passing the focus request to the viewer's control.
	 */
	public void setFocus() {
		viewer.getControl().setFocus();
	}

	private Job evaluation;
	
	private void setFeatureModelEditor(IWorkbenchPart activeEditor) {
		if (featureModelEditor != null && featureModelEditor == activeEditor)
			return;

		if (featureModelEditor != null) {
			featureModelEditor.getOriginalFeatureModel().removeListener(
					modelListener);
			featureModelEditor.getFeatureModel().removeListener(modelListener);
			featureModelEditor = null;
		}

		if (activeEditor instanceof FeatureModelEditor) {
			featureModelEditor = (FeatureModelEditor) activeEditor;
			featureModelEditor.getOriginalFeatureModel().addListener(
					modelListener);
			featureModelEditor.getFeatureModel().addListener(modelListener);
			
			setWorkspaceRoot(featureModelEditor);
			
			if (evaluation == null
					&& featureModelEditor.getGrammarFile().getResource()
							.getProject().getName()
							.startsWith("EvaluationTest")) {
				evaluation = new Job("Evaluation Test") {
					@Override
					protected IStatus run(IProgressMonitor monitor) {
						Evaluation.evaluate(featureModelEditor.getGrammarFile()
								.getResource().getProject());
						return Status.OK_STATUS;
					}
				};
				evaluation.setPriority(Job.LONG);
				evaluation.schedule();
				UIJob conversion = new UIJob("Converting Feature Models") {
					@Override
					public IStatus runInUIThread(IProgressMonitor monitor) {
						try {
							convertModelToBitmapTest(featureModelEditor
									.getGrammarFile().getResource()
									.getProject().getFolder("models"));
						} catch (Exception e) {
							FMUIPlugin.getDefault().logError(e);
						}
						return Status.OK_STATUS;
					}

					public void convertModelToBitmapTest(IFolder folder)
							throws CoreException {
						for (IResource res : folder.members())
							if (res instanceof IFile
									&& res.getName().endsWith(".m")) {
								IFile fmFile = (IFile) res;
								try {
									FeatureModel fm = new FeatureModel();
									//XmlFeatureModelReader reader = new XmlFeatureModelReader(fm,fmFile.getProject());
									FeatureModelReaderIFileWrapper reader = new FeatureModelReaderIFileWrapper(new XmlFeatureModelReader(
											fm,fmFile.getProject()));
									
									reader.readFromFile(fmFile);

									String imageName = fmFile.getRawLocation()
											.toOSString();
									imageName = imageName.substring(0,
											imageName.length() - ".m".length())
											+ ".png";
									createBitmap(fm, new File(imageName));
								} catch (FileNotFoundException e) {
									FMUIPlugin.getDefault().logError(e);
								} catch (UnsupportedModelException e) {
									FMUIPlugin.getDefault().logError(e);
								}
							}
						folder.refreshLocal(IResource.DEPTH_ONE, null);
					}

					private void createBitmap(FeatureModel featureModel,
							File file) {
						IPersistentPropertyManager manager = featureModel.getPersistentPropertyManager();
						GraphicalViewerImpl graphicalViewer = new ScrollingGraphicalViewer();
						graphicalViewer.createControl(viewer.getControl()
								.getParent());
						graphicalViewer.getControl().setBackground(DIAGRAM_BACKGROUND);
						graphicalViewer
								.setEditPartFactory(new GraphicalEditPartFactory());
						ScalableFreeformRootEditPart rootEditPart = new ScalableFreeformRootEditPart();
						((ConnectionLayer) rootEditPart
								.getLayer(LayerConstants.CONNECTION_LAYER))
								.setAntialias(SWT.ON);
						graphicalViewer.setRootEditPart(rootEditPart);
						graphicalViewer.setContents(featureModel);
						FeatureDiagramLayoutManager layoutManager = new LevelOrderLayout(manager);
						layoutManager.layout(featureModel);
						GEFImageWriter.writeToFile(graphicalViewer, file);
					}
				};
				conversion.setPriority(Job.LONG);
				conversion.schedule();
			}
		}
		refresh();
	}

	private void setWorkspaceRoot(FeatureModelEditor editor) {
		if (workspaceRoot == null) {
			workspaceRoot = editor.getGrammarFile().getResource().getProject().getWorkspace().getRoot();
		}
	}

	private void refresh() {
		try {
			if (job != null) {
				job.join();
			}
		} catch (InterruptedException e) {
			FMUIPlugin.getDefault().logError(e);
		}
			
		job = new Job("Updating Feature Model Edits") {
			@Override
			protected IStatus run(IProgressMonitor monitor) {
				if (workspaceRoot != null) {
					activatorAction.setEnabled(true);
					activatorAction.setChecked(isActivatorChecked());
					manualAction.setEnabled(isActivatorChecked());
				}
				if (featureModelEditor == null) {
					contentProvider.defaultContent();
				} else if (isActivatorChecked()) {
					contentProvider.defaultManualContent();
				} else {
					contentProvider.calculateContent(
							featureModelEditor.getOriginalFeatureModel(),
							featureModelEditor.getFeatureModel());
				}
				return Status.OK_STATUS;
			}
		};
		job.setPriority(Job.LONG);
		job.schedule();
	}

	public TreeViewer getViewer() {
		return viewer;
	}

}
