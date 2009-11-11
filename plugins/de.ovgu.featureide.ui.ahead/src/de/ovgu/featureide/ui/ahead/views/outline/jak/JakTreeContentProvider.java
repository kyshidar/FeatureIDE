package de.ovgu.featureide.ui.ahead.views.outline.jak;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.ui.part.FileEditorInput;

import featureide.core.CorePlugin;
import featureide.core.IFeatureProject;
import featureide.core.jakprojectmodel.IClass;
import featureide.core.jakprojectmodel.IJakModelElement;
import featureide.core.jakprojectmodel.IJakProjectModel;

/**
 * This class is part of the outline. It provides the content that
 * should be displayed. Therefor it maps the information provided
 * by the jakprojectmodel to the methods of the ITreeContentProvider
 * interface.
 * 
 * @author Tom Brosch
 * @author Thomas Th�m
 *
 */
public class JakTreeContentProvider implements ITreeContentProvider {
	
	private IFile jakfile = null;

	private IJakProjectModel jakProject = null;

	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof IJakModelElement)
			return ((IJakModelElement) parentElement).getChildren();

		return null;
	}

	public Object getParent(Object element) {
		if (element instanceof IJakModelElement)
			((IJakModelElement) element).getParent();
		return null;
	}

	public boolean hasChildren(Object element) {
		if (element instanceof IJakModelElement)
			return ((IJakModelElement) element).hasChildren();
		return false;
	}

	public Object[] getElements(Object inputElement) {

		if (jakProject != null) {
			IClass c = jakProject.getClass(jakfile);
			if (c != null)
				return new IClass[] { jakProject.getClass(jakfile) };
			else
				return new String[] { "No ast available" };
		}

		return new String[] { "No project data available" }; //ticket #99 old code: return null;
	}

	public void dispose() {
	}

	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		if (newInput != null && newInput instanceof FileEditorInput) {
			IFile file = ((FileEditorInput) newInput).getFile();
			IFeatureProject featureProject = CorePlugin.getProjectData(file);
			if (featureProject != null) {
				jakfile = file;
				jakProject = featureProject.getJakProjectModel();
			}
		}
	}
}
